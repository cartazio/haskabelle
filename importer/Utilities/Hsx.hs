{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Munich

Auxiliary.
-}

module Importer.Utilities.Hsx ( 
  namesFromHsDecl, bindingsFromDecls, bindingsFromPats, 
  extractBindingNs, extractFreeVarNs, letify,
  Renaming, renameFreeVars, renameHsDecl,
  freshIdentifiers, isFreeVar, srcloc2string, qualify,
  orderDeclsBySourceLine, getSourceLine,
) where
  
import Maybe
import List (tails, sort)
import Array (inRange)

import Control.Monad.State
import Data.Generics.PlateData
import Language.Haskell.Hsx


import Importer.Utilities.Misc (concatMapM, assert)
import Importer.Utilities.Gensym

qualify :: Module -> HsQName -> HsQName
qualify _ (Qual m n) = Qual m n
qualify m (UnQual n) = Qual m n

srcloc2string :: SrcLoc -> String
srcloc2string (SrcLoc { srcFilename=filename, srcLine=line, srcColumn=column })
    = filename ++ ":" ++ (show line) ++ ":" ++ (show column)


namesFromHsDecl :: HsDecl -> Maybe [HsQName]

namesFromHsDecl (HsTypeDecl _ name _ _)        = Just [UnQual name]
namesFromHsDecl (HsDataDecl _ _ name _ _ _)    = Just [UnQual name]
namesFromHsDecl (HsNewTypeDecl _ _ name _ _ _) = Just [UnQual name]
namesFromHsDecl (HsClassDecl _ _ name _ _ _)   = Just [UnQual name]
namesFromHsDecl (HsInstDecl _ _ qname _ _)     = Just [qname]
namesFromHsDecl (HsTypeSig _ names _)          = Just (map UnQual names)
namesFromHsDecl (HsInfixDecl _ _ _ ops)        = Just [UnQual n | n <- (universeBi ops :: [HsName])]
namesFromHsDecl (HsPatBind _ pat _ _)          = Just (bindingsFromPats [pat])
namesFromHsDecl (HsFunBind (m:ms))             = case m of 
                                                   HsMatch _ fname _ _ _ -> Just [UnQual fname]
namesFromHsDecl _                              = Nothing

class HasBindings a where
    extractBindingNs :: a -> [HsQName]

instance HasBindings a => HasBindings [a] where
    extractBindingNs list = concatMap extractBindingNs list

instance HasBindings HsPat where
    extractBindingNs pattern = bindingsFromPats [pattern]

instance HasBindings HsDecl where
    extractBindingNs decl = bindingsFromDecls [decl] 

instance HasBindings HsBinds where
    extractBindingNs (HsBDecls decls) = extractBindingNs decls


bindingsFromPats          :: [HsPat] -> [HsQName]
bindingsFromPats pattern  = [ UnQual n | HsPVar n <- universeBi pattern ] 

bindingsFromDecls       :: [HsDecl] -> [HsQName]
bindingsFromDecls decls = assert (not (hasDuplicates bindings)) bindings
    -- Type signatures do not create new bindings, but simply annotate them.
    where bindings = concatMap (fromJust . namesFromHsDecl) (filter (not . isTypeSig) decls)
          isTypeSig (HsTypeSig _ _ _) = True
          isTypeSig _                 = False

hasDuplicates :: Eq a => [a] -> Bool
hasDuplicates list = or (map (\(x:xs) -> x `elem` xs) tails')
    where tails' = filter (not . null) (tails list)


class Letifiable a where
    letify' :: HsBinds -> a -> a
    letify  :: HsBinds -> a -> a
    letify (HsBDecls []) body = body
    letify bindings body      = letify' bindings body

instance Letifiable HsExp where
    letify' bindings body = HsLet bindings body

instance Letifiable HsRhs where
    letify' bindings (HsUnGuardedRhs body)  = HsUnGuardedRhs (letify bindings body)


type Renaming = (HsQName, HsQName)

freshIdentifiers :: [HsQName] -> State GensymCount [Renaming]
freshIdentifiers qnames
    = do freshs <- mapM genHsQName qnames
         return (zip qnames freshs)


shadow :: [HsQName] -> [Renaming] -> [Renaming]
shadow boundNs renamings  = filter ((`notElem` boundNs) . fst) renamings

qtranslate :: [Renaming] -> HsQName -> HsQName
qtranslate renamings qname 
    = fromMaybe qname (lookup qname renamings)

translate :: [Renaming] -> HsName -> HsName
translate renamings name 
    = let (UnQual name') = qtranslate renamings (UnQual name) in name'

qoptranslate :: [Renaming] -> HsQOp -> HsQOp
qoptranslate renamings qop
    = case qop of HsQVarOp qname -> HsQVarOp (qtranslate renamings qname)
                  HsQConOp qname -> HsQConOp (qtranslate renamings qname)

optranslate :: [Renaming] -> HsOp -> HsOp
optranslate renamings op
    = case op of HsVarOp qname -> HsVarOp (translate renamings qname)
                 HsConOp qname -> HsConOp (translate renamings qname)


class AlphaConvertable a where
    renameFreeVars :: [Renaming] -> a -> a

instance AlphaConvertable HsOp where
    renameFreeVars renams op
        = case op of HsVarOp name -> HsVarOp (translate renams name)
                     HsConOp name -> HsConOp (translate renams name)

instance AlphaConvertable HsExp where
    renameFreeVars renams hsexp
        = case hsexp of
            HsVar qname -> HsVar (qtranslate renams qname)
            HsCon qname -> HsVar (qtranslate renams qname)
            HsLit lit   -> HsLit lit
            HsInfixApp e1 qop e2
                -> HsInfixApp e1' qop' e2'
                     where e1'  = renameFreeVars renams e1
                           qop' = qoptranslate renams qop
                           e2'  = renameFreeVars renams e2
            HsLambda loc pats body
                -> HsLambda loc pats body'
                     where body' = let boundNs = bindingsFromPats pats
                                   in renameFreeVars (shadow boundNs renams) body
            HsCase exp alternatives
                -> HsCase exp' alternatives'
                     where declNs        = bindingsFromDecls (childrenBi alternatives :: [HsDecl])
                           renams'       = shadow declNs renams
                           exp'          = renameFreeVars renams' exp
                           alternatives' = map (renameFreeVars renams') alternatives
            HsLet (HsBDecls decls) body 
                -> HsLet (HsBDecls decls') body'
                      where declNs  = bindingsFromDecls decls
                            renams' = shadow declNs renams
                            body'   = renameFreeVars renams' body
                            decls'  = map (renameFreeVars renams') decls
            HsRecConstr qname updates
                -> HsRecConstr qname updates
            HsRecUpdate exp updates
                -> HsRecUpdate (renameFreeVars renams exp) updates
            exp -> assert (isTriviallyDescendable exp)
                     $ descendBi (renameFreeVars renams :: HsExp -> HsExp) exp

isTriviallyDescendable hsexp 
    = case hsexp of
        HsApp      _ _   -> True
        HsNegApp   _     -> True
        HsIf       _ _ _ -> True
        HsTuple    _     -> True
        HsList     _     -> True
        HsParen    _     -> True
        _                -> False -- rest is not supported at the moment.



instance AlphaConvertable HsDecl where
    renameFreeVars renams hsdecl
        = case hsdecl of
            HsFunBind matchs        -> HsFunBind $ map (renameFreeVars renams) matchs
            HsTypeSig loc names typ -> HsTypeSig loc names typ
            HsPatBind loc pat (HsUnGuardedRhs body) binds
                -> HsPatBind loc pat (HsUnGuardedRhs body') binds'
                      where (HsLet binds' body') = renameFreeVars renams' (HsLet binds body)
                            renams' = shadow (bindingsFromPats [pat]) renams


instance AlphaConvertable HsAlt where
    renameFreeVars renams hsalt@(HsAlt _ pat _ _)
        = fromHsPatBind (renameFreeVars renams (toHsPatBind hsalt))

toHsPatBind (HsAlt loc pat guards wherebinds)
    = HsPatBind loc pat (guards2rhs guards) wherebinds
  where guards2rhs (HsUnGuardedAlt body) = HsUnGuardedRhs body

fromHsPatBind (HsPatBind loc pat rhs wherebinds)
    = HsAlt loc pat (rhs2guards rhs) wherebinds
  where rhs2guards (HsUnGuardedRhs body) = HsUnGuardedAlt body


instance AlphaConvertable HsMatch where
    renameFreeVars renams (HsMatch loc name pats rhs (HsBDecls decls))
        = HsMatch loc name pats rhs' (HsBDecls decls')
      where patNs  = extractBindingNs pats
            declNs = extractBindingNs decls 
            rhs'   = renameFreeVars (shadow ([UnQual name] ++ patNs ++ declNs) renams) rhs
            decls' = map (renameFreeVars (shadow (UnQual name : declNs) renams)) decls

instance AlphaConvertable HsBinds where
    renameFreeVars renams (HsBDecls decls) = HsBDecls decls'
        where declNs = extractBindingNs decls
              decls' = map (renameFreeVars (shadow declNs renams)) decls

instance AlphaConvertable HsRhs where
    renameFreeVars renams (HsUnGuardedRhs exp)
        = HsUnGuardedRhs (renameFreeVars renams exp)



renameHsDecl :: [Renaming] -> HsDecl -> HsDecl

renameHsDecl renams (HsTypeDecl loc tyconN tyvarNs typ)
    = HsTypeDecl loc (translate renams tyconN) tyvarNs typ

renameHsDecl renams (HsDataDecl loc context tyconN tyvarNs condecls derives)
    = HsDataDecl loc context (translate renams tyconN) tyvarNs condecls derives

renameHsDecl renams (HsInfixDecl loc assoc prio ops)
    = HsInfixDecl loc assoc prio (map (optranslate renams) ops)

renameHsDecl renams (HsTypeSig loc names typ)
    = HsTypeSig loc (map (translate renams) names) typ

renameHsDecl renams (HsFunBind matchs)
    = HsFunBind (map rename matchs)
      where rename (HsMatch loc name pats rhs wbinds)
                = HsMatch loc (translate renams name) pats rhs wbinds

renameHsDecl renams (HsPatBind loc pat rhs wbinds)
    = HsPatBind loc (renameHsPat renams pat) rhs wbinds


renameHsPat :: [Renaming] -> HsPat -> HsPat

renameHsPat renams pat
    = case pat of
        HsPVar name                 -> HsPVar (translate renams name)
        HsPLit lit                  -> HsPLit lit
        HsPNeg pat                  -> HsPNeg (renameHsPat renams pat)
        HsPInfixApp pat1 qname pat2 -> HsPInfixApp pat1' qname' pat2'
            where pat1'  = renameHsPat renams pat1 
                  qname' = qtranslate renams qname
                  pat2'  = renameHsPat renams pat2
        HsPApp qname pats           -> HsPApp qname' pats'
            where qname' = qtranslate renams qname
                  pats'  = map (renameHsPat renams) pats
        HsPTuple pats               -> HsPTuple (map (renameHsPat renams) pats)
        HsPList  pats               -> HsPList (map (renameHsPat renams) pats)
        HsPParen pat                -> HsPParen (renameHsPat renams pat)


-- Kludge.
--
isFreeVar qname body
    = occurs qname body && let body' = renameFreeVars (runGensym 999 (freshIdentifiers [qname])) body
                           in not (occurs qname body')
    where occurs qname body 
              = not (null [ qn | HsVar qn <- universeBi body, qn == qname ])

extractFreeVarNs thing
    = filter (flip isFreeVar thing) (universeBi thing :: [HsQName])

orderDeclsBySourceLine :: HsDecl -> HsDecl -> Ordering
orderDeclsBySourceLine decl1 decl2
    = compare (getSourceLine decl1) (getSourceLine decl2) 

getSourceLine :: HsDecl -> Int
getSourceLine decl
    = let srclocs = childrenBi decl :: [SrcLoc]
          lines   = map srcLine srclocs
      in head (sort lines)

foo = [HsFunBind
        [HsMatch
           (SrcLoc{srcFilename = "/tmp/test.hs", srcLine = 8, srcColumn = 1})
           (HsIdent "g")
           [HsPVar (HsIdent "x")]
           (HsUnGuardedRhs
              (HsLet
                 (HsBDecls
                    [HsPatBind
                       (SrcLoc{srcFilename = "/tmp/test.hs", srcLine = 8, srcColumn = 11})
                       (HsPVar (HsIdent "a"))
                       (HsUnGuardedRhs (HsLit (HsInt 42)))
                       (HsBDecls [])])
                 (HsInfixApp (HsVar (UnQual (HsIdent "a")))
                    (HsQVarOp (UnQual (HsSymbol "*")))
                    (HsVar (UnQual (HsIdent "x"))))))
           (HsBDecls [])]]