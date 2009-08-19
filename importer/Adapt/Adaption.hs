{-| Author: Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Adapt.Adaption (adaptGlobalEnv, adaptIsaUnit) where

import Maybe
import List (partition)

import Control.Monad.State
import qualified Data.Map as Map

import qualified Importer.LexEnv as Env
import Importer.ConversionUnit
import Importer.Utilities.Misc

import Importer.Adapt.Mapping (AdaptionTable(..))

import qualified Importer.Isa as Isa
import Language.Haskell.Exts


data AdptState = AdptState { oldGlobalEnv     :: Env.GlobalE,
                             adaptedGlobalEnv :: Env.GlobalE,
                             adaptionTable    :: AdaptionTable,
                             currentModuleID  :: Maybe Env.ModuleID
                           }

type AdaptM v = State AdptState v

getAdptState :: AdaptM AdptState
getAdptState = do s <- get; return s

query :: (AdptState -> x) -> AdaptM x
query slot = do s <- getAdptState; return (slot s)

set :: (AdptState -> AdptState) -> AdaptM ()
set update = do s <- getAdptState; put (update s); return ()

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
--   \([a', b', c']) -> body
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
                         

runAdaptionWith :: AdaptM v -> AdptState -> v
runAdaptionWith adaption state
    = evalState adaption state

runAdaption :: Env.GlobalE -> Env.GlobalE -> AdaptionTable -> AdaptM v -> v
runAdaption oldEnv newEnv tbl adaption 
    = runAdaptionWith adaption (AdptState { oldGlobalEnv     = oldEnv,
                                            adaptedGlobalEnv = newEnv,
                                            adaptionTable    = tbl,
                                            currentModuleID  = Nothing 
                                          })


qualifyConstantName :: Env.GlobalE -> Env.ModuleID -> Env.EnvName -> Env.EnvName
qualifyConstantName globalEnv mID name
    = fromMaybe (Env.qualifyEnvName mID name)
        $ Env.resolveConstantName globalEnv mID name

qualifyTypeName :: Env.GlobalE -> Env.ModuleID -> Env.EnvName -> Env.EnvName
qualifyTypeName globalEnv mID name
    = fromMaybe (Env.qualifyEnvName mID name)
        $ Env.resolveTypeName globalEnv mID name


adaptGlobalEnv :: AdaptionTable -> Env.GlobalE -> Env.GlobalE
adaptGlobalEnv tbl env
    = Env.updateGlobalEnv 
        (\n -> case translateName tbl n of 
                 Just new_id -> [new_id]
                 Nothing     -> adapt_type_in_identifier env tbl n)
        env

translateName :: AdaptionTable -> Env.EnvName -> Maybe Env.Identifier
translateName (AdaptionTable mappings) name
    = lookupBy (\n1 id2 -> n1 == Env.identifier2name id2) name mappings

translateIdentifier :: AdaptionTable -> Env.Identifier -> Env.Identifier
translateIdentifier tbl id
    = case translateName tbl (Env.identifier2name id) of
        Nothing     -> id
        Just new_id -> new_id

adapt_type_in_identifier :: Env.GlobalE -> AdaptionTable -> Env.EnvName -> [Env.Identifier]
adapt_type_in_identifier globalEnv tbl n@(Env.EnvQualName mID _)
    = let old_ids      = Env.lookupIdentifiers_OrLose mID n globalEnv
          old_lexinfos = map Env.lexInfoOf old_ids
          old_types    = map Env.typeOf old_lexinfos
          new_types    = catMaybes (zipWith translate old_types old_lexinfos)
          new_lexinfos = zipWith (\t lxinf -> lxinf {Env.typeOf = t}) new_types old_lexinfos
      in 
        zipWith Env.updateIdentifier old_ids new_lexinfos
    where 
      translate typ lexinfo
          = translateEnvType tbl (qualifyTypeName globalEnv (Env.moduleOf lexinfo)) typ

translateEnvType :: AdaptionTable -> (Env.EnvName -> Env.EnvName) -> Env.EnvType -> Maybe Env.EnvType
translateEnvType (AdaptionTable mappings) qualify typ
    = let type_renams   = filter (Env.isData . fst) mappings
          type_renams'  = assert (all (Env.isData . snd) type_renams) 
                            $ map (\(t1,t2) -> (Env.identifier2name t1, Env.identifier2name t2)) 
                                  type_renams
          class_renams  = filter (Env.isClass . fst) mappings
          class_renams' = assert (all (Env.isClass . snd) class_renams)
                            $ map (\(c1,c2) -> (Env.identifier2name c1, Env.identifier2name c2))
                                  class_renams
          renamings     = type_renams' ++ class_renams'
      in 
        case runState (translate renamings typ) False of
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
                     Env.EnvTyScheme ctx t
                        -> do let (tyvarNs, classNss) = unzip ctx
                              tyvarNs'  <- mapM transl tyvarNs
                              classNss' <- mapM (mapM transl) classNss
                              t'        <- translate alist t
                              let ctx'   = zip tyvarNs' classNss'
                              return (Env.EnvTyScheme ctx' t')

adaptEnvName :: Env.EnvName -> AdaptM Env.EnvName
adaptEnvName n 
    = do Just mID <- query currentModuleID
         tbl      <- query adaptionTable
         oldEnv   <- query oldGlobalEnv
         newEnv   <- query adaptedGlobalEnv
         case Env.lookupConstant mID n oldEnv of
           Nothing -> return n
           Just id -> let new_id       = translateIdentifier tbl id
                          new_id_name  = Env.identifier2name new_id
                      in assert (isJust (Env.lookupConstant mID new_id_name newEnv))
                           $ return new_id_name

adaptEnvType :: Env.EnvType -> AdaptM Env.EnvType
adaptEnvType t
    = do Just mID <- query currentModuleID
         tbl      <- query adaptionTable
         oldEnv   <- query oldGlobalEnv
         let qualify n = qualifyTypeName oldEnv mID n
         return (fromMaybe t (translateEnvType tbl qualify t))

adaptName :: Isa.Name -> AdaptM Isa.Name
adaptName n = do
  n' <- adaptEnvName (Env.fromIsa n)
  return (Env.toIsa n')

adaptType :: Isa.Type -> AdaptM Isa.Type
adaptType t = do t' <- adaptEnvType (Env.fromIsa t); return (Env.toIsa t')

adaptClass :: Isa.Name -> AdaptM Isa.Name
adaptClass classN = do let ignore = Isa.Name "_"
                       t <- adaptType (Isa.TyScheme [(ignore, [classN])] Isa.TyNone)
                       let (Isa.TyScheme [(_, [classN'])] _) = t
                       return classN'

adaptIsaUnit :: AdaptionTable -> Env.GlobalE -> IsaUnit -> IsaUnit
adaptIsaUnit adaptionTable globalEnv (IsaUnit thycmds custThys adaptedGlobalEnv)
    = let run thunk = runAdaption globalEnv adaptedGlobalEnv adaptionTable thunk
          thycmds'  = run (mapM adapt thycmds)
      in IsaUnit thycmds' custThys adaptedGlobalEnv


not_implemented x = error ("Adaption not implemented yet for\n  " ++ prettyShow' "thing" x) 

class Adapt a where
    adapt  :: a -> AdaptM a

instance Adapt Isa.DatatypeDef where
    adapt (Isa.DatatypeDef sig@(Isa.TypeSpec tyvarNs tycoN) constrs)    
        = shadowing (tycoN:tyvarNs) $
            do constrs' <- mapM adpt constrs
               return (Isa.DatatypeDef sig constrs')
        where adpt (Isa.Constructor name types)
                  = do types' <- mapM adaptType types
                       return (Isa.Constructor name types')

instance Adapt Isa.Cmd where
    adapt (Isa.Block cmds)       
        = mapM adapt cmds >>= (return . Isa.Block)

    adapt (Isa.TheoryCmd thy imps cmds)   
        = do old_mID <- query currentModuleID
             set (setModuleID $ Just (Env.fromIsa thy))
             cmds'   <- mapM adapt cmds
             set (setModuleID old_mID)
             return (Isa.TheoryCmd thy imps cmds')
        where setModuleID v state
                  = state { currentModuleID = v }

    adapt (Isa.TypesCmd aliases) = liftM Isa.TypesCmd (mapM adpt aliases)
        where adpt (spec,typ) = liftM2 (,) (return spec) (adaptType typ)
    adapt c@(Isa.RecordCmd _ _)      = not_implemented c
    adapt c@(Isa.InfixDeclCmd _ _ _) = not_implemented c
    adapt c@(Isa.Comment _)          = return c

    adapt (Isa.DatatypeCmd defs)    
        = liftM Isa.DatatypeCmd $ mapM adapt defs
                           
    adapt (Isa.FunCmd funNs typesigs defs)
        = do funNs' <- mapM adaptName funNs
             typesigs' <- mapM adapt typesigs
             shadowing funNs $
               do defs' <- mapM (\(funN, pats, body)
                                     -> do funN' <- adaptName funN
                                           assert (funN `elem` funNs && funN' `elem` funNs') $ return ()
                                           pats' <- mapM adapt pats
                                           shadowing (concatMap extractNames pats') $
                                             do body' <- adapt body ; return (funN', pats', body'))
                                defs
                  return (Isa.FunCmd funNs' typesigs' defs')
         
    adapt (Isa.PrimrecCmd funNs typesigs defs)
        = do funNs' <- mapM adaptName funNs
             typesigs' <- mapM adapt typesigs
             shadowing funNs $
               do defs' <- mapM (\(funN, pats, body)
                                     -> do funN' <- adaptName funN
                                           assert (funN `elem` funNs && funN' `elem` funNs') $ return ()
                                           pats' <- mapM adapt pats
                                           shadowing (concatMap extractNames pats') $
                                             do body' <- adapt body ; return (funN', pats', body'))
                                defs
                  return (Isa.PrimrecCmd funNs' typesigs' defs')

    adapt (Isa.DefinitionCmd name typesig (pat, term))
        = do typesig' <- adapt typesig
             shadowing (extractNames pat) $
               do term' <- adapt term ; return (Isa.DefinitionCmd name typesig' (pat, term'))

    adapt (Isa.ClassCmd classN supclassNs typesigs)
        = do classN'     <- adaptClass classN
             supclassNs' <- mapM adaptClass supclassNs
             typesigs'   <- mapM adapt typesigs
             return (Isa.ClassCmd classN' supclassNs' typesigs')

    adapt (Isa.InstanceCmd classN typ cmds)
        = do classN' <- adaptClass classN
             shadowing [classN'] $ do typ'  <- adaptType typ
                                      cmds' <- mapM adapt cmds
                                      return (Isa.InstanceCmd classN' typ' cmds')

instance Adapt Isa.TypeSpec where
    adapt (Isa.TypeSpec tyvarNs tycoN)
        = do (Isa.Type tycoN' tyvars') <- adaptType (Isa.Type tycoN (map Isa.TyVar tyvarNs))
             return $ Isa.TypeSpec (map (\(Isa.TyVar n) -> n) tyvars') tycoN'

instance Adapt Isa.TypeSig where
    adapt (Isa.TypeSig n t)
        = do t' <- adaptType t ; return (Isa.TypeSig n t')

instance Adapt Isa.Term where
    adapt (Isa.Literal lit)     = return (Isa.Literal lit)

    adapt (Isa.Const n)           = adaptConst n >>= (return . Isa.Const)
      where
        adaptConst n = do
          n' <- adaptEnvName (Env.fromIsa n)
          return (Env.toIsa n')

    adapt (Isa.Parenthesized t) = adapt t     >>= (return . Isa.Parenthesized)

    adapt (Isa.App t1 t2)       = do Just mID <- query currentModuleID
                                     oldEnv   <- query oldGlobalEnv
                                     newEnv   <- query adaptedGlobalEnv
                                     t1'      <- adapt t1 
                                     t2'      <- adapt t2
                                     -- t1 may have been an InfixOp and was adapted to
                                     -- a function. In this case, we have to make sure that
                                     -- all the arguments passed to this function are 
                                     -- parenthesized.
                                     let n1   = find_applied_op t1
                                     let n1'  = find_applied_op t1'
                                     case (n1, n1') of 
                                       (Just n1, Just n1')
                                           -> if isInfixOp mID n1 oldEnv && not (isInfixOp mID n1' newEnv)
                                              then return $ Isa.App t1' (Isa.Parenthesized t2')
                                              else return $ Isa.App t1' t2'
                                       _   -> return (Isa.App t1' t2')
        where isInfixOp mID n env
                  = case Env.lookupConstant mID (Env.fromIsa n) env of
                      Nothing -> False
                      Just c  -> Env.isInfixOp c
              find_applied_op :: Isa.Term -> Maybe Isa.Name
              find_applied_op t 
                  = case t of
                      Isa.Const n            -> Just n
                      Isa.App t1 t2        -> find_applied_op t1
                      Isa.Parenthesized t' -> find_applied_op t'
                      _                    -> Nothing -- the remaining cases are 
                                                      -- too complicated, so we give up.

    adapt (Isa.If c t e)        = do c' <- adapt c ; t' <- adapt t ; e' <- adapt e
                                     return (Isa.If c' t' e')

    adapt (Isa.Abs boundN body)
        = shadowing [boundN] $
            adapt body >>= (return . Isa.Abs boundN)

    adapt (Isa.Let bindings body)
        = do pats' <- mapM adapt (map fst bindings)
             nested_binding (zipWith (\p' t -> (extractNames p', adapt t))
                                     pats' (map snd bindings)) $
               \terms' -> do body' <- adapt body
                             return (Isa.Let (zip pats' terms') body')

    adapt (Isa.Case term patterns)
        = do term'     <- adapt term
             patterns' <- mapM (\(pat, body) 
                                    -> do pat' <- adapt pat
                                          shadowing (extractNames pat') $
                                            do body' <- adapt body
                                               return (pat', body'))
                               patterns
             return (Isa.Case term' patterns')

    adapt (Isa.ListComp body stmts) = adpt body stmts []
      where 
        adpt e [] stmts' = do e' <- adapt e; return (Isa.ListComp e' (reverse stmts'))
        adpt e (Isa.Guard b : rest) stmts'
            = adapt b >>= (\b' -> adpt e rest (Isa.Guard b':stmts'))
        adpt e (Isa.Generator (pat, exp) : rest) stmts'
            = do pat' <- adapt pat
                 exp' <- adapt exp
                 shadowing (extractNames pat') $ 
                   adpt e rest (Isa.Generator (pat', exp') : stmts')
    adapt (Isa.DoBlock pre stmts post) = 
        do stmts' <- mapM adapt stmts
           return $ Isa.DoBlock pre stmts' post

instance Adapt Isa.Stmt where
    adapt (Isa.DoGenerator pat exp) = liftM2 Isa.DoGenerator (adapt pat) (adapt exp)
    adapt (Isa.DoQualifier exp) = liftM Isa.DoQualifier $ adapt exp

               
extractNames :: Isa.Term -> [Isa.Name]
extractNames (Isa.Const n)                   = [n]
extractNames (Isa.App t1 t2)               = extractNames t1 ++ extractNames t2
extractNames etc = []

