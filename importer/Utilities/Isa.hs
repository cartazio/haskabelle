{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Munich

Auxiliary.
-}

module Importer.Utilities.Isa (
  alphaConvertTerm, alphaConvertCmd,
) where

import Maybe (fromMaybe)
import Data.Generics.PlateData
import Importer.IsaSyntax


-- getBoundVarsFromCmd :: Cmd -> Maybe [Name]
-- getBoundVarsFromCmd cmd = bindings cmd
--  where bindings (FunCmd fname _ _)       = Just [fname]
--        bindings (Block cmds)             = liftM concat (sequence (map bindings cmds))
--        bindings (DefinitionCmd name _ _) = Just [name]
--        bindings (InfixDeclCmd opN _ _)   = Just [opN]
--        bindings (Comment _)              = Just []
--        bindings _                        = Nothing


alphaConvertTerm :: Theory -> [(Name, Name)] -> Term -> Term

alphaConvertTerm thy alist term = aconvert (map (\(k,v) -> (canonicalize thy k, v)) alist) term
    where aconvert alist term
              = case term of
                  Var n             -> Var (translate n alist thy)
                  App t1 t2         -> apply2 App $ map (aconvert alist) [t1, t2]
                  If c t e          -> apply3 If  $ map (aconvert alist) [c, t, e]
                  Parenthesized t   -> Parenthesized (aconvert alist t)
                  Lambda vars body
                      -> let boundvs = map (canonicalize thy) vars
                         in aconvert (shadow boundvs alist) body
                  RecConstr recordN updates
                      -> let recordN'       = translate recordN alist thy
                             (names, terms) = unzip updates
                             names'         = map (\n -> translate n alist thy) names
                             terms'         = map (aconvert alist) terms
                         in RecConstr recordN' (zip names' terms')
                  RecUpdate term updates
                      -> let term'          = aconvert alist term
                             (names, terms) = unzip updates
                             names'         = map (\n -> translate n alist thy) names
                             terms'         = map (aconvert alist) terms
                         in RecUpdate term' (zip names' terms')
                  Case term matches
                      -> Case (aconvert alist term) (map cnv matches)
                         where cnv (pat, term)
                                   = let boundvs = map (canonicalize thy) [ n | Var n <- universeBi pat]
                                     in (pat, aconvert (shadow boundvs alist) term)

alphaConvertCmd  :: Theory -> [(Name, Name)] -> Cmd  -> Cmd

alphaConvertCmd thy alist cmd = aconvert (map (\(k,v) -> (canonicalize thy k, v)) alist) cmd
    where aconvert alist cmd
              = case cmd of
                  Block cmds                -> Block $ map (aconvert alist) cmds
                  TheoryCmd theoryN cmds    -> TheoryCmd theoryN  $ map (alphaConvertCmd theoryN alist) cmds
                  DatatypeCmd tyspec dspecs -> DatatypeCmd tyspec $ map cnv dspecs
                      where cnv (Constructor conN types)
                                = Constructor (translate conN alist thy) types
                  RecordCmd tspec slotspecs -> RecordCmd tspec (map cnv slotspecs)
                      where cnv (slotN, slotTy)
                                = (translate slotN alist thy, slotTy)
                  FunCmd fname sig matches  
                      -> FunCmd (translate fname alist thy) 
                                (aconvertSig alist sig)
                                (map (aconvertMatch alist) matches)
                  DefinitionCmd name tsig match 
                      -> DefinitionCmd (translate name alist thy) 
                                       (aconvertSig alist tsig)
                                       (aconvertMatch alist match)
                  InfixDeclCmd opN assoc prio 
                      -> InfixDeclCmd (translate opN alist thy) assoc prio
                  TypesCmd specs -> TypesCmd specs
                  Comment  str   -> Comment str
          aconvertMatch alist (pats, term)
              = let boundvs = map (canonicalize thy) [ n | Var n <- universeBi pats]
                in (pats, alphaConvertTerm thy (shadow boundvs alist) term)
          aconvertSig alist (TypeSig name typ)
              = TypeSig (translate name alist thy) typ


canonicalize, decanonicalize :: Theory -> Name -> Name

canonicalize _ (QName t n)     = QName t n
canonicalize thy (Name n)      = QName thy n

decanonicalize thy (QName t n) = if (t == thy) then Name n else QName t n
decanonicalize _ (Name n)      = Name n

shadow :: [Name] -> [(Name, Name)] -> [(Name, Name)]
shadow vars alist = filter ((`notElem` vars) . fst) alist
          
translate :: Name -> [(Name, Name)] -> Theory -> Name
translate name alist thy
    = decanonicalize thy (fromMaybe name (lookup (canonicalize thy name) alist))

apply2 f [a,b]     = f a b
apply3 f [a,b,c]   = f a b c
