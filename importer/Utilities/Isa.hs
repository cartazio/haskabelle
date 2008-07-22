{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen

Auxiliary.
-}

module Importer.Utilities.Isa 
    (renameIsaCmd, namesFromIsaCmd, renameTyVarInType,
     mk_InstanceCmd_name) where

import Control.Monad.State
import Maybe
import Data.Generics.Biplate (universeBi)

import Importer.IsaSyntax

renameTyVarInType :: Theory -> (Name, Name) -> Type -> Type
renameTyVarInType thy (from, to) typ
    = let from' = canonicalize thy from
          to'   = canonicalize thy to
      in case typ of
           TyVar vN    -> TyVar (translate thy [(from', to')] vN)
           TyCon cN ts -> TyCon cN $ map (renameTyVarInType thy (from, to)) ts
           TyFun t1 t2 -> TyFun (renameTyVarInType thy (from,to) t1) 
                                (renameTyVarInType thy (from,to) t2)
           TyTuple ts  -> TyTuple $ map (renameTyVarInType thy (from, to)) ts
           TyNone      -> TyNone

renameIsaCmd :: Theory -> [(Name, Name)] -> Cmd -> Cmd
renameIsaCmd thy renamings cmd
    = let rs = canonicalizeRenamings thy renamings
      in case cmd of
           FunCmd ns tysigs clauses -> FunCmd ns' tysigs clauses'
               where ns'      = map (translate thy rs) ns
                     clauses' = map (renameClause rs) clauses
                     renameClause rs (n, pats, body) 
                         = (translate thy rs n, pats, alphaConvertTerm thy rs body)

           DefinitionCmd n sig (p, t) -> DefinitionCmd n' sig (p', t')
               where n' = translate thy rs n
                     p' = alphaConvertTerm thy rs p
                     t' = alphaConvertTerm thy rs t

           _ -> error ("renameIsaCmd: Fall through: " ++ show cmd)


alphaConvertTerm :: Theory -> [(Name, Name)] -> Term -> Term

alphaConvertTerm thy alist term = aconvert (canonicalizeRenamings thy alist) term
    where 
      aconvert alist term
          = case term of
              Literal l         -> Literal l
              Var n             -> Var (translate thy alist n)
              App t1 t2         -> apply2 App $ map (aconvert alist) [t1, t2]
              If c t e          -> apply3 If  $ map (aconvert alist) [c, t, e]
              Parenthesized t   -> Parenthesized (aconvert alist t)
              Let binds body    -> Let binds' body'
                  where
                    body' = aconvert (shadow boundvs alist) body
                    (binds', boundvs)
                        -- A let expression binds sequentially in Isar/HOL.
                        -- We remember all currently bound variables in a state.
                        = flip runState []
                            $ foldM (\r (p, t) 
                                         -> do let new_bound_vs = map (canonicalize thy) (pat_to_boundNs p)
                                               old_bound_vs <- get
                                               let boundvs = new_bound_vs ++ old_bound_vs
                                               put boundvs
                                               return (r ++ [(p, aconvert (shadow boundvs alist) t)]))
                                     [head binds]
                                     (tail binds)

              Lambda var body
                  -> let boundvs = [canonicalize thy var]
                     in aconvert (shadow boundvs alist) body
              RecConstr recordN updates
                  -> let recordN'       = translate thy alist recordN
                         (names, terms) = unzip updates
                         names'         = map (\n -> translate thy alist n) names
                         terms'         = map (aconvert alist) terms
                     in RecConstr recordN'(zip names' terms')
              RecUpdate term updates
                  -> let term'          = aconvert alist term
                         (names, terms) = unzip updates
                         names'         = map (\n -> translate thy alist n) names
                         terms'         = map (aconvert alist) terms
                     in RecUpdate term' (zip names' terms')
              Case term matches
                  -> Case (aconvert alist term) (map cnv matches)
                      where cnv (pat, term)
                                = let boundvs = map (canonicalize thy) (pat_to_boundNs pat)
                                  in (pat, aconvert (shadow boundvs alist) term)

pat_to_boundNs (Var n)           = [n]
pat_to_boundNs (App p1 p2)       = pat_to_boundNs p1 ++ pat_to_boundNs p2
pat_to_boundNs (Parenthesized p) = pat_to_boundNs p
pat_to_boundNs _                 = []

canonicalizeRenamings thy renamings
    = map (\(k,v) -> (canonicalize thy k, v)) renamings

canonicalize, decanonicalize :: Theory -> Name -> Name

canonicalize _ (QName t n)     = QName t n
canonicalize thy (Name n)      = QName thy n

decanonicalize thy (QName t n) = if (t == thy) then Name n else QName t n
decanonicalize _ (Name n)      = Name n

shadow :: [Name] -> [(Name, Name)] -> [(Name, Name)]
shadow vars alist = filter ((`notElem` vars) . fst) alist
          
translate :: Theory -> [(Name, Name)] -> Name -> Name
translate thy alist name
    = decanonicalize thy (fromMaybe name (lookup (canonicalize thy name) alist))

apply2 f [a,b]     = f a b
apply3 f [a,b,c]   = f a b c


namesFromIsaCmd :: Cmd -> [Name]
namesFromIsaCmd (FunCmd ns _ _)       = ns
namesFromIsaCmd (DefinitionCmd n _ _) = [n]
namesFromIsaCmd junk 
    = error ("namesFromIsaCmd: Fall through: " ++ show junk)

name2str (QName _ s) = s
name2str (Name s)    = s

mk_InstanceCmd_name :: Name -> Type -> Name
mk_InstanceCmd_name (QName t n) (TyCon conN [])
    = QName t (concat [n, "_", name2str conN])
mk_InstanceCmd_name (Name n) (TyCon conN [])
    = Name (concat [n, "_", name2str conN])

                    