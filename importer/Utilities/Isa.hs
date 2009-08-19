{-| Author: Tobias C. Rittweiler, TU Muenchen

Auxiliary.
-}

module Importer.Utilities.Isa 
    (renameIsaCmd, namesFromIsaCmd, renameTyVarInType,
     mk_InstanceCmd_name) where

import Control.Monad.State
import Maybe
import Data.Generics.Biplate (universeBi)

import qualified Importer.Isa as Isa

renameTyVarInType :: Isa.ThyName -> (Isa.Name, Isa.Name) -> Isa.Type -> Isa.Type
renameTyVarInType thy (from, to) typ
    = let from' = canonicalize thy from
          to'   = canonicalize thy to
      in case typ of
           Isa.TyVar vN    -> Isa.TyVar (translate thy [(from', to')] vN)
           Isa.Type cN ts -> Isa.Type cN $ map (renameTyVarInType thy (from, to)) ts
           Isa.TyFun t1 t2 -> Isa.TyFun (renameTyVarInType thy (from,to) t1) 
                                (renameTyVarInType thy (from,to) t2)
           Isa.TyTuple ts  -> Isa.TyTuple $ map (renameTyVarInType thy (from, to)) ts
           Isa.TyNone      -> Isa.TyNone

renameIsaCmd :: Isa.ThyName -> [(Isa.Name, Isa.Name)] -> Isa.Cmd -> Isa.Cmd
renameIsaCmd thy renamings cmd
    = let rs = canonicalizeRenamings thy renamings
      in case cmd of
           Isa.FunCmd ns tysigs clauses -> Isa.FunCmd ns' tysigs clauses'
               where ns'      = map (translate thy rs) ns
                     clauses' = map (renameClause rs) clauses
                     renameClause rs (n, pats, body) 
                         = (translate thy rs n, pats, alphaConvertTerm thy rs body)

           Isa.DefinitionCmd n sig (p, t) -> Isa.DefinitionCmd n' sig (p', t')
               where n' = translate thy rs n
                     p' = alphaConvertTerm thy rs p
                     t' = alphaConvertTerm thy rs t

           _ -> error ("renameIsaCmd: Fall through: " ++ show cmd)


alphaConvertTerm :: Isa.ThyName -> [(Isa.Name, Isa.Name)] -> Isa.Term -> Isa.Term

alphaConvertTerm thy alist term = aconvert (canonicalizeRenamings thy alist) term
    where 
      aconvert alist term
          = case term of
              Isa.Literal l         -> Isa.Literal l
              Isa.Const n             -> Isa.Const (translate thy alist n)
              Isa.App t1 t2         -> apply2 Isa.App $ map (aconvert alist) [t1, t2]
              Isa.If c t e          -> apply3 Isa.If  $ map (aconvert alist) [c, t, e]
              Isa.Parenthesized t   -> Isa.Parenthesized (aconvert alist t)
              Isa.Let binds body    -> Isa.Let binds' body'
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

              Isa.Abs var body
                  -> let boundvs = [canonicalize thy var]
                     in aconvert (shadow boundvs alist) body
              Isa.RecConstr recordN updates
                  -> let recordN'       = translate thy alist recordN
                         (names, terms) = unzip updates
                         names'         = map (\n -> translate thy alist n) names
                         terms'         = map (aconvert alist) terms
                     in Isa.RecConstr recordN'(zip names' terms')
              Isa.RecUpdate term updates
                  -> let term'          = aconvert alist term
                         (names, terms) = unzip updates
                         names'         = map (\n -> translate thy alist n) names
                         terms'         = map (aconvert alist) terms
                     in Isa.RecUpdate term' (zip names' terms')
              Isa.Case term matches
                  -> Isa.Case (aconvert alist term) (map cnv matches)
                      where cnv (pat, term)
                                = let boundvs = map (canonicalize thy) (pat_to_boundNs pat)
                                  in (pat, aconvert (shadow boundvs alist) term)

pat_to_boundNs (Isa.Const n)           = [n]
pat_to_boundNs (Isa.App p1 p2)       = pat_to_boundNs p1 ++ pat_to_boundNs p2
pat_to_boundNs (Isa.Parenthesized p) = pat_to_boundNs p
pat_to_boundNs _                 = []

canonicalizeRenamings thy renamings
    = map (\(k,v) -> (canonicalize thy k, v)) renamings

canonicalize, decanonicalize :: Isa.ThyName -> Isa.Name -> Isa.Name

canonicalize _ (Isa.QName t n)     = Isa.QName t n
canonicalize thy (Isa.Name n)      = Isa.QName thy n

decanonicalize thy (Isa.QName t n) = if (t == thy) then Isa.Name n else Isa.QName t n
decanonicalize _ (Isa.Name n)      = Isa.Name n

shadow :: [Isa.Name] -> [(Isa.Name, Isa.Name)] -> [(Isa.Name, Isa.Name)]
shadow vars alist = filter ((`notElem` vars) . fst) alist
          
translate :: Isa.ThyName -> [(Isa.Name, Isa.Name)] -> Isa.Name -> Isa.Name
translate thy alist name
    = decanonicalize thy (fromMaybe name (lookup (canonicalize thy name) alist))

apply2 f [a,b]     = f a b
apply3 f [a,b,c]   = f a b c


namesFromIsaCmd :: Isa.Cmd -> [Isa.Name]
namesFromIsaCmd (Isa.FunCmd ns _ _)       = ns
namesFromIsaCmd (Isa.DefinitionCmd n _ _) = [n]
namesFromIsaCmd junk 
    = error ("namesFromIsaCmd: Fall through: " ++ show junk)

name2str (Isa.QName _ s) = s
name2str (Isa.Name s)    = s

mk_InstanceCmd_name :: Isa.Name -> Isa.Type -> Isa.Name
mk_InstanceCmd_name (Isa.QName t n) (Isa.Type conN [])
    = Isa.QName t (concat [n, "_", name2str conN])
mk_InstanceCmd_name (Isa.Name n) (Isa.Type conN [])
    = Isa.Name (concat [n, "_", name2str conN])

                    