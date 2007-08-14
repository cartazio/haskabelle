{-  ID:         $Id: Printer.hs 421 2007-08-03 19:18:11Z rittweil $
    Author:     Tobias C. Rittweiler, TU Munich

Auxiliary.
-}

module Importer.Utilities.Hsx ( 
  namesFromHsBinds, namesFromHsDecl,
  bindingsFromDecls,
  alphaconvert,
) where

import Importer.Utilities.Misc (concatMapM, assert)

import Data.Generics.PlateData
import Language.Haskell.Hsx
import Control.Monad.State
import Maybe

namesFromHsBinds :: HsBinds -> Maybe [HsQName]

namesFromHsBinds (HsBDecls decls) 
    = concatMapM namesFromHsDecl decls


namesFromHsDecl :: HsDecl -> Maybe [HsQName]

namesFromHsDecl (HsTypeDecl _ name _ _)        = Just [UnQual name]
namesFromHsDecl (HsDataDecl _ _ name _ _ _)    = Just [UnQual name]
namesFromHsDecl (HsNewTypeDecl _ _ name _ _ _) = Just [UnQual name]
namesFromHsDecl (HsClassDecl _ _ name _ _ _)   = Just [UnQual name]
namesFromHsDecl (HsInstDecl _ _ qname _ _)     = Just [qname]
namesFromHsDecl (HsTypeSig _ names _)          = Just (map UnQual names)
namesFromHsDecl (HsInfixDecl _ _ _ ops)        = Just [UnQual n | n <- (universeBi ops :: [HsName])]
namesFromHsDecl (HsPatBind _ pat _ _)          = Just [UnQual n | n <- (universeBi pat :: [HsName])]
namesFromHsDecl (HsFunBind (m:ms))             = case m of 
                                                   HsMatch _ fname _ _ _ -> Just [UnQual fname]
namesFromHsDecl _                              = Nothing



bindingsFromPats modul pattern 
    = [ Qual modul n | HsPVar n <- universeBi pattern ] 

bindingsFromDecls modul decls 
    -- Type signatures do not create new bindings, but simply 
    -- annotate them.
    = concatMap (fromJust . namesFromHsDecl) (filter (not . isTypeSig) decls)
    where isTypeSig (HsTypeSig _ _ _) = True
          isTypeSig _                 = False



type Renaming = (HsQName, HsQName)

qtranslate :: HsQName -> [Renaming] -> HsQName
qtranslate qname renamings 
    = fromMaybe qname (lookup qname renamings)

translate :: HsName -> [Renaming] -> HsName
translate name renamings 
    = let (UnQual name') = qtranslate (UnQual name) renamings in name'

shadow :: [HsQName] -> [Renaming] -> [Renaming]
shadow boundNs renamings  = filter ((`notElem` boundNs) . fst) renamings


class AlphaConvertable a where
    alphaconvert :: (AlphaConvertable a) => Module -> [Renaming] -> a -> a 


instance AlphaConvertable HsExp where
    alphaconvert modul renams hsexp
        = case hsexp of
            HsVar qname -> HsVar $ qtranslate qname renams
            HsCon qname -> HsVar $ qtranslate qname renams
            HsLit lit   -> HsLit lit
            HsRecConstr qname updates
                -> HsRecConstr (qtranslate qname renams) updates'
                     where updates' = map (alphaconvert modul renams) updates
            HsRecUpdate exp updates
                -> HsRecUpdate exp' updates'
                     where exp'     = alphaconvert modul renams exp
                           updates' = map (alphaconvert modul renams) updates
            HsLambda loc pats body
                -> HsLambda loc pats body'
                     where body' = let boundNs = bindingsFromPats modul pats in 
                                   alphaconvert modul (shadow boundNs renams) body
            HsCase exp alternatives
                -> HsCase exp' alternatives'
                     where exp'          = alphaconvert modul renams exp
                           alternatives' = map (alphaconvert modul renams) alternatives
            HsLet (HsBDecls decls) body 
                -> HsLet (HsBDecls decls') body'
                      where declNs  = bindingsFromDecls modul decls
                            renams' = shadow declNs renams
                            body'   = alphaconvert modul renams' body
                            decls'  = map (alphaconvert modul renams') decls
            exp -> assert (isTriviallyDescendable exp)
                     $ descendBi (alphaconvert modul renams :: HsExp -> HsExp) exp

isTriviallyDescendable hsexp 
    = case hsexp of
        HsInfixApp _ _ _ -> True
        HsApp      _ _   -> True
        HsNegApp   _     -> True
        HsIf       _ _ _ -> True
        HsTuple    _     -> True
        HsList     _     -> True
        HsParen    _     -> True
        _                -> False -- rest is not supported at the moment.


instance AlphaConvertable HsDecl where
    alphaconvert modul renams hsdecl
        = case hsdecl of
            HsFunBind matchs        -> HsFunBind $ map (alphaconvert modul renams) matchs
            HsTypeSig loc names typ -> HsTypeSig loc [translate n renams | n <- names] typ
            HsPatBind loc pat (HsUnGuardedRhs body) binds
                -> HsPatBind loc pat' (HsUnGuardedRhs body') binds'
                      where pat'                 = alphaconvert modul renams pat
                            (HsLet binds' body') = alphaconvert modul renams (HsLet binds body)


instance AlphaConvertable HsFieldUpdate where
    alphaconvert modul renams (HsFieldUpdate slotN exp)
        = HsFieldUpdate slotN (alphaconvert modul renams exp)


instance AlphaConvertable HsAlt where
    alphaconvert modul renams hsalt@(HsAlt _ pat _ _)
        = let renams' = shadow (bindingsFromPats modul [pat]) renams
          in fromHsPatBind (alphaconvert modul renams' (toHsPatBind hsalt))

toHsPatBind (HsAlt loc pat guards wherebinds)
    = HsPatBind loc pat (guards2rhs guards) wherebinds
  where guards2rhs (HsUnGuardedAlt body) = HsUnGuardedRhs body

fromHsPatBind (HsPatBind loc pat rhs wherebinds)
    = HsAlt loc pat (rhs2guards rhs) wherebinds
  where rhs2guards (HsUnGuardedRhs body) = HsUnGuardedAlt body
        

instance AlphaConvertable HsMatch where
    alphaconvert modul renams (HsMatch loc name pats (HsUnGuardedRhs body) (HsBDecls decls))
        = HsMatch loc name' pats (HsUnGuardedRhs body') (HsBDecls decls')
      where name'  = translate name renams
            patNs  = bindingsFromPats  modul pats
            declNs = bindingsFromDecls modul decls 
            body'  = alphaconvert modul (shadow (patNs ++ declNs) renams) body
            decls' = map (alphaconvert modul (shadow declNs renams)) decls


instance AlphaConvertable HsPat where
    alphaconvert modul renams pat = transformBi alpha pat
      where alpha (HsPVar name) = HsPVar (translate name renams)
            alpha etc           = etc



-- preprocess :: HsModule -> HsModule

-- preprocess (HsModule loc modul exports imports topdecls)
--       = HsModule loc modul exports imports (topdecls ++ localdecls' ++ decls_of_localdecls)
--   where localdecls = concat [ decls | HsBDecls decls <- (childrenBi topdecls :: [HsBinds]) ]            
--         (localdecls', decls_of_localdecls) = unzip (map (delocalize modul) localdecls)



-- uniquefy modul body decls
--     = let declNs    = bindingsFromDecls modul decls
--           renamings = zip declNs (map (genHsQName 99) declNs)
--           body'     = alphaconvert modul renamings body
--           decls'    = map (alphaconvert modul renamings) decls
--       in (body', decls')

-- delocalize modul (HsPatBind loc pat (HsUnGuardedRhs body) (HsBDecls decls))
--     = let (body', decls') = uniquefy modul body decls
--           (decls'', decls_of_decls) = unzip (map delocalize decls')
--       in (HsPatBind loc pat (HsUnGuardedRhs body') (HsBDecls []), decls'' ++ decls_of_decls)

-- genHsName n (HsIdent  prefix) = HsIdent  (prefix ++ "_" ++ (show n))
-- genHsName n (HsSymbol prefix) = HsSymbol (prefix ++ "_" ++ (show n))

-- genHsQName n  (Qual m prefix) = Qual m (genHsName n prefix)
-- genHsQName n  (UnQual prefix) = UnQual (genHsName n prefix)


-- f modul (HsPatBind loc pat (HsUnGuardedRhs body) (HsBDecls decls)) 
--     = do (n:ns,result) <- get
--          let declNs    = bindingsFromDecls modul decls
--          let renamings = zip declNs (map (genHsQName n) declNs)
--          let body'     = alphaconvert modul renamings body
--          decls' <- descendBiM (f modul) decls
--          let decls''    = 
--          put (ns, decls'' ++ result)
--          return (HsPatBind loc pat (HsUnGuardedRhs body') (HsBDecls []))
-- f modul (HsMatch loc name pats (HsUnGuardedRhs) (HsBDecls decls))
--   = return (HsMatch loc name pats (HsUnGuardedRhs) (HsBDecls decls))

-- delocalizeHsDecl (HsFunBind matchs)
--      = concatMap delocalizeHsMatch matchs
--    where delocalizeHsMatch (HsMatch loc name pats rhs (HsBDecl localdecls))
--              = 
