{-# LANGUAGE PatternGuards #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen

Pretty printing of abstract Isar/HOL theory.
-}

module Importer.Printer (pprint) where

import Maybe
import Control.Monad

import qualified Text.PrettyPrint as P

import Importer.Utilities.Misc
import Importer.Utilities.Isa (renameIsaCmd, namesFromIsaCmd, 
                               mk_InstanceCmd_name)

import Language.Haskell.Exts.Syntax as Hsx (SpecialCon(..), QName(..))

import qualified Importer.IsaSyntax as Isa
import qualified Importer.LexEnv as Env

import Importer.Adapt.Mapping (AdaptionTable(..))


data PPState = PPState { globalEnv        :: Env.GlobalE,
                         currentTheory    :: Isa.Theory,
                         -- Are we in an Infix Application?
                         currentAppFlavor :: Maybe AppFlavor,
                         currentTyScheme  :: [(Isa.Name, [Isa.Name])],
                         -- If True, we're already in doubly-quoted section.
                         withinHOL        :: Bool
                       }

data DocM v = DocM (PPState -> (v, PPState))

emptyPPState = PPState { globalEnv = Env.initialGlobalEnv,
                         currentTheory = Isa.Theory "Scratch",
                         currentAppFlavor = Nothing,
                         currentTyScheme = [],
                         withinHOL = False
                       }

instance Monad DocM where
    return value = DocM (\state -> (value, state))
    DocM sf0 >>= f
        = DocM $ \s0 -> let (v1, s1) = sf0 s0
                            DocM sf1 = f v1
                            (v2, s2) = sf1 s1 in (v2, s2)

queryPP :: (PPState -> field) -> DocM field
queryPP query
    = DocM $ \pps -> (query pps, pps)

updatePP :: (PPState -> PPState) -> DocM ()
updatePP update
    = DocM $ \pps -> ((), update pps)

type Doc = DocM P.Doc

-- The pretty printing combinators

empty :: Doc
empty = return P.empty

nest :: Int -> Doc -> Doc
nest i dm = dm >>= return . P.nest i


-- Literals

text, ptext :: String -> Doc
text  = return . P.text
ptext = return . P.text

char :: Char -> Doc
char = return . P.char

int :: Int -> Doc
int = return . P.int

integer :: Integer -> Doc
integer = return . P.integer

float :: Float -> Doc
float = return . P.float

double :: Double -> Doc
double = return . P.double

rational :: Rational -> Doc
rational = return . P.rational


-- Constants

semi,comma,colon,space,equals,dot,apostroph,asterisk :: Doc
semi   = return P.semi
comma  = return P.comma
colon  = return P.colon
space  = return P.space
equals = return P.equals

dot       = char '.'
apostroph = char '\''
asterisk  = char '*'
plus      = char '+'

lparen,rparen,lbrack,rbrack,lbrace,rbrace :: Doc
lparen = return  P.lparen
rparen = return  P.rparen
lbrack = return  P.lbrack
rbrack = return  P.rbrack
lbrace = return  P.lbrace
rbrace = return  P.rbrace


-- Simple Combining Forms

parens, brackets, braces, quotes, doubleQuotes, bananas, blankline :: Doc -> Doc
parens d       = d >>= return . P.parens
brackets d     = d >>= return . P.brackets
braces d       = d >>= return . P.braces
quotes d       = d >>= return . P.quotes
doubleQuotes d = d >>= return . P.doubleQuotes

bananas d      = text "(|" <+> d <+> text "|)"
blankline d    = space $$ d

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

withCurrentTheory :: Isa.Theory -> Doc -> Doc
withCurrentTheory thy d
    = do oldthy <- queryPP (\pps -> currentTheory pps)
         updatePP (\pps -> pps { currentTheory = thy })
         result <- d
         updatePP (\pps -> pps { currentTheory = thy })
         return result

maybeWithinHOL :: Doc -> Doc
maybeWithinHOL d   
    = do within_p <- queryPP withinHOL
         if within_p then d
                     else do updatePP (\pps -> pps { withinHOL = True })
                             result <- doubleQuotes d
                             updatePP (\pps -> pps { withinHOL = False })
                             return result

withinHOL_if :: Bool -> Doc -> Doc
withinHOL_if pred doc
    | pred = do within_p <- queryPP withinHOL
                if within_p then doc
                            else do updatePP (\pps -> pps { withinHOL = True })
                                    result <- doubleQuotes doc
                                    updatePP (\pps -> pps { withinHOL = False })
                                    return result
    | otherwise = doc

withinApplication :: AppFlavor -> Doc -> Doc
withinApplication app d
    = do old_app <- queryPP (\pps -> currentAppFlavor pps)
         updatePP (\pps -> pps { currentAppFlavor = Just app })
         result <- d
         updatePP (\pps -> pps { currentAppFlavor = old_app })
         return result


withTyScheme :: [(Isa.Name, [Isa.Name])] -> Doc -> Doc
withTyScheme ctx d
    = do old_ctx <- queryPP (\pps -> currentTyScheme pps)
         updatePP (\pps -> pps { currentTyScheme = ctx })
         result <- d
         updatePP (\pps -> pps { currentTyScheme = old_ctx })
         return result

comment :: Doc -> Doc
comment d = text "(*" <+> d <+> text "*)"

-- fill-paragraph str = vcat $ map text (lines str)

-- Combinators

(<>),(<+>),($$),($+$) :: Doc -> Doc -> Doc
(<>) = liftM2 (P.<>)
(<+>) = liftM2 (P.<+>)
($$) = liftM2 (P.$$)
($+$) = liftM2 (P.$+$)

ncat, hcat,hsep,vcat,sep,cat,fsep,fcat :: [Doc] -> Doc
ncat = foldr ($+$) empty
hcat dl = sequence dl >>= return . P.hcat
hsep dl = sequence dl >>= return . P.hsep
vcat dl = sequence dl >>= return . P.vcat
sep dl  = sequence dl >>= return . P.sep
cat dl  = sequence dl >>= return . P.cat
fsep dl = sequence dl >>= return . P.fsep
fcat dl = sequence dl >>= return . P.fcat

-- Some More

hang :: Doc -> Int -> Doc -> Doc
hang dM i rM = do{d<-dM; r<-rM; return $ P.hang d i r}

punctuate :: Doc -> [Doc] -> [Doc]
punctuate _ []      = []
punctuate p (d1:ds) = go d1 ds
                    where go d [] = [d]
                          go d (e:es) = (d <> p) : go e es

accentuate :: Doc -> [Doc] -> [Doc]
accentuate d list = map (d<>) list

indent = 3

class Printer a where
    pprint' :: AdaptionTable -> [String] -> a -> DocM P.Doc
    pprint  :: AdaptionTable -> [String] -> Env.GlobalE -> a -> P.Doc
    pprint adapt reserved env obj = let
      DocM sf = pprint' adapt reserved obj
      (doc, _state) = sf (emptyPPState { globalEnv = env })
      in doc

instance Printer Isa.DatatypeDef where
    pprint' adapt reserved (Isa.DatatypeDef tyspec dataspecs)
        = pprint' adapt reserved tyspec 
          <+> vcat (zipWith (<+>) (equals : repeat (char '|'))
                                  (map ppconstr dataspecs))
          where ppconstr (Isa.Constructor con types) 
                    = hsep $ pprint' adapt reserved con : map (pprint' adapt reserved) types


instance Printer Isa.Cmd where
    pprint' adapt reserved (Isa.Comment string) = empty -- blankline $ comment string
    pprint' adapt reserved (Isa.Block cmds)     = blankline $ vcat $ map (pprint' adapt reserved) cmds
    pprint' adapt reserved (Isa.TheoryCmd thy imps cmds)
        = do env <- queryPP globalEnv
             let imps' = map (pprint' adapt reserved) (imps ++ [Isa.Theory Env.prelude])
             withCurrentTheory thy $
               text "theory" <+> pprint' adapt reserved thy $+$
               text "imports " <> fsep  imps'    $+$
               text "begin"                                      $+$
               (vcat $ map (pprint' adapt reserved) cmds)                         $+$
               text "\nend"

    pprint' adapt reserved (Isa.DatatypeCmd (def:defs)) = 
        let fstDef = text "datatype" <+> pprint' adapt reserved def
            restDefs = map ((text "and     " <+>) . pprint' adapt reserved) defs
        in blankline $ vcat (fstDef:restDefs)
          

    pprint' adapt reserved (Isa.RecordCmd tyspec conspecs)
        = blankline $
          text "record" <+> pprint' adapt reserved tyspec <+> equals $$
          space <+> vcat (map pp conspecs)
          where pp (slotName, slotType) = pprint' adapt reserved slotName <+> text "::" <+> pprint' adapt reserved slotType

    pprint' adapt reserved (Isa.DefinitionCmd vname tysig matching)
        = case matching of
            (pat, term)
                -> blankline $
                   text "definition" <+> ppHeader vname tysig $$
                   text "where" $$
                   space <+> (maybeWithinHOL $ ppEquation pat term)
        where 
          ppHeader n sig
              | isEmptySig sig = pprint' adapt reserved n
              | otherwise      = pprint' adapt reserved n <+> text "::" <+> maybeWithinHOL (pprint' adapt reserved sig)
          ppEquation pat term
              = do thy <- queryPP currentTheory 
                   env <- queryPP globalEnv
                   let lookup = (\n -> lookupIdentifier thy n env)
                   pprint' adapt reserved pat <+> equals <+> parensIf (isCompound adapt term lookup) (pprint' adapt reserved term)

    pprint' adapt reserved (Isa.PrimrecCmd fnames tysigs equations)
        = printFunDef adapt reserved "primrec" fnames tysigs equations

    pprint' adapt reserved (Isa.FunCmd fnames tysigs equations)
        = printFunDef adapt reserved "fun" fnames tysigs equations

    pprint' adapt reserved (Isa.ClassCmd classN superclassNs typesigs)
        = blankline $
          text "class" <+> pprint' adapt reserved classN 
                       <+> equals 
                       <+> hsep (punctuate plus (map (pprint' adapt reserved) superclassNs))
                       <+> (if null superclassNs || null typesigs then empty else plus) $$
          space <> space <> vcat (zipWith (<+>) (repeat (text "fixes"))
                                                (map ppSig typesigs))
        where ppSig (Isa.TypeSig n t)
                  = pprint' adapt reserved n <+> text "::" <+> pprint' adapt reserved t
          
    pprint' adapt reserved (Isa.InstanceCmd classN typ cmds)
        = do thy <- queryPP currentTheory
             let cmds' = map (renameInstanceCmd thy typ) cmds
             blankline $
               text "instantiation" <+> pprint' adapt reserved typ <+> text "::" <+> pprint' adapt reserved classN $$
               text "begin" $$
               space <> space <> vcat (map (pprint' adapt reserved) cmds') $$
               (blankline $
                text "instance .." $$
                text "end")
        where
          renameInstanceCmd thy t c
              = let renams = [ (n, mk_InstanceCmd_name n t) | n <- namesFromIsaCmd c ]
                in renameIsaCmd thy renams c
 
    pprint' adapt reserved (Isa.InfixDeclCmd op assoc prio)
        = comment $ text "infix" <> pp assoc <+> int prio <+> pprint' adapt reserved op
          where pp Isa.AssocNone  = text ""
                pp Isa.AssocLeft  = text "l"
                pp Isa.AssocRight = text "r"
    
    pprint' adapt reserved (Isa.TypesCmd aliases) = text "types" <+> vcat (map pp aliases)
        where pp (spec, typ) = pprint' adapt reserved spec <+> equals <+> pprint' adapt reserved typ

printFunDef adapt reserved cmd fnames tysigs equations
    = blankline $
      text cmd <+> vcat (punctuate (text " and ") (map ppHeader (zip fnames tysigs))) $$
      text "where" $$
      vcat (zipWith (<+>) (space : repeat (char '|'))
            (map ppEquation equations))
    where 
      ppHeader (fn, sig)
          | isEmptySig sig = pprint' adapt reserved fn
          | otherwise      = pprint' adapt reserved fn <+> text "::" <+> maybeWithinHOL (pprint' adapt reserved sig)
      ppEquation (fname, pattern, term) 
          = do thy <- queryPP currentTheory 
               env <- queryPP globalEnv
               let lookup = (\n -> lookupIdentifier thy n env)
               maybeWithinHOL $
                              pprint' adapt reserved fname <+> 
                              hsep (map (pprint' adapt reserved) pattern) <+> 
                              equals <+> 
                              parensIf (isCompound adapt term lookup) (pprint' adapt reserved term)

instance Printer Isa.Theory where
    pprint' adapt reserved (Isa.Theory name) =
      text (map (\c -> if c == '.' then '_' else c) name)
      -- FIXME need uniform rename of theory names

instance Printer Isa.TypeSpec where
    pprint' adapt reserved (Isa.TypeSpec [] tycon)
        = pprint' adapt reserved tycon
    pprint' adapt reserved (Isa.TypeSpec tyvars tycon)
        = let tyvars' = parens . hsep . punctuate comma . accentuate apostroph $ 
                        map (pprint' adapt reserved) tyvars
          in tyvars' <+> pprint' adapt reserved tycon

instance Printer Isa.Name where
    pprint' adapt reserved n@(Isa.Name _)      = pprintName reserved n
    pprint' adapt reserved (Isa.QName _ str)   = pprintName reserved (Isa.Name str) -- FIXME

pprintName reserved n@(Isa.Name str) = withinHOL_if (isReservedKeyword str) 
      $ do thy <- queryPP currentTheory 
           env <- queryPP globalEnv
           app <- queryPP currentAppFlavor
           case app of
             Just (InfixApp _ _ _) -> text str
             _  -> let lookup = (\n -> lookupIdentifier thy n env)
                   in if (isInfixOp n lookup || isUnaryOp n lookup)
                      then parens $ text "op" <+> text str
                      else text str
      where
        isReservedKeyword :: String -> Bool
        isReservedKeyword str = str `elem` reserved

instance Printer Isa.Type where
    pprint' adapt reserved (Isa.TyNone)      = text ""
    pprint' adapt reserved (Isa.TyVar vname) 
        = do alist <- queryPP currentTyScheme
             let tyvar_doc = apostroph <> pprint' adapt reserved vname
             case lookup vname alist of
               Nothing       -> tyvar_doc
               Just [classN] -> parens (tyvar_doc <+> text "::" <+> pprint' adapt reserved classN)
               Just classNs  
                   -> parens $ tyvar_doc <+> 
                               text "::" <+> 
                               (braces . vcat . punctuate comma . map (pprint' adapt reserved) $ classNs)

    pprint' adapt reserved (Isa.TyCon cname []) = pprint' adapt reserved cname 
    pprint' adapt reserved (Isa.TyCon cname tyvars) 
        = do maybeWithinHOL $
               hsep (map pp tyvars) <+> pprint' adapt reserved cname
          where pp tyvar = parensIf (isCompoundType tyvar) (pprint' adapt reserved tyvar)

    pprint' adapt reserved (Isa.TyScheme [] t)  = pprint' adapt reserved t
    pprint' adapt reserved (Isa.TyScheme ctx t) = withTyScheme ctx (pprint' adapt reserved t)

    pprint' adapt reserved (Isa.TyFun t1 t2)
        = maybeWithinHOL $
            case t1 of Isa.TyFun _ _ -> parens (pprint' adapt reserved t1) <+> text "=>" <+> pprint' adapt reserved t2
                       _             -> pprint' adapt reserved t1          <+> text "=>" <+> pprint' adapt reserved t2

    pprint' adapt reserved (Isa.TyTuple types)
        = maybeWithinHOL $
            hsep (punctuate (space<>asterisk) (map (pprint' adapt reserved) types))


instance Printer Isa.TypeSig where
    pprint' adapt reserved (Isa.TypeSig _name typ) = pprint' adapt reserved typ

instance Printer Isa.Literal where
    -- We annotate Integer literals explicitly to be of our sort "num"
    -- (cf. Prelude.thy), because otherwise Isabelle's type inference
    -- would come up with a too general type, resulting in
    -- non-workingness.
    pprint' adapt reserved (Isa.Int i)      = let cc = colon <> colon in
                               integer i
                               -- parens $ integer i  <> cc <> text "_" <> cc <> text "num"
    pprint' adapt reserved (Isa.Char ch)    = text "CHR " <+> quotes (quotes (char ch))
    pprint' adapt reserved (Isa.String str) = quotes . quotes . text $ str

instance Printer Isa.Term where
    pprint' adapt reserved (Isa.Var vname)         = pprint' adapt reserved vname
    pprint' adapt reserved (Isa.Literal lit)       = pprint' adapt reserved lit
    pprint' adapt reserved (Isa.Parenthesized t)   
        = do thy <- queryPP currentTheory 
             env <- queryPP globalEnv
             let lookup = (\n -> lookupIdentifier thy n env)
             parensIf (not (isSelfEvaluating adapt t lookup)) 
               $ pprint' adapt reserved t

    pprint' adapt reserved app @ (Isa.App t1 t2)   
        = do thy <- queryPP currentTheory 
             env <- queryPP globalEnv
             let lookup = (\n -> lookupIdentifier thy n env)
             let flavor = categorizeApp adapt app lookup
             withinApplication flavor $
               case flavor of
                 ListApp  l      -> pprintAsList adapt reserved l
                 TupleApp l      -> pprintAsTuple adapt reserved l
                 InfixApp x op y -> let x' = parensIf (isCompound adapt x lookup) $ pprint' adapt reserved x
                                        y' = parensIf (isCompound adapt y lookup) $ pprint' adapt reserved y
                                    in  x' <+> pprint' adapt reserved op <+> y'
                 FunApp          -> pprint' adapt reserved t1 <+> parensIf (isCompound adapt t2 lookup) (pprint' adapt reserved t2)
                 UnaryOpApp      -> pprint' adapt reserved t1 <+> parensIf (isCompound adapt t2 lookup) (pprint' adapt reserved t2)

    pprint' adapt reserved (Isa.If t1 t2 t3)
        = fsep [text "if"   <+> pprint' adapt reserved t1,
                text "then" <+> pprint' adapt reserved t2,
                text "else" <+> pprint' adapt reserved t3]

    pprint' adapt reserved lexpr@(Isa.Lambda _ _)
        = let (argNs, body) = flattenLambdas lexpr in 
          fsep [text "%" <+> hsep (map (pprint' adapt reserved) argNs) <+> dot,
                nest 2 (pprint' adapt reserved body)]

    pprint' adapt reserved (Isa.RecConstr recordN updates)
        = pprint' adapt reserved recordN <+> (bananas . vcat . punctuate comma $ map pp updates)
          where pp (vname, typ) = pprint' adapt reserved vname <+> equals <+> pprint' adapt reserved typ

    pprint' adapt reserved (Isa.RecUpdate term updates)
        = pprint' adapt reserved term <+> (bananas . vcat . punctuate comma $ map pp updates)
          where pp (vname, typ) = pprint' adapt reserved vname <+> text ":=" <+> pprint' adapt reserved typ

    pprint' adapt reserved (Isa.Case term matchs)
         = hang (text "case" <+> pprint' adapt reserved term <+> text "of")
                1
                (vcat $ zipWith (<+>) (space : repeat (char '|'))
                                      (map pp matchs))
           where pp (pat, term) = (pprint' adapt reserved pat) <+> text "=>" <+> pprint' adapt reserved term


    pprint' adapt reserved (Isa.Let bindings body)
        = text "let" <+> vcat (punctuate semi (map ppBinding bindings))
                   $$ text "in" <+> pprint' adapt reserved body
          where ppBinding (pat, term)
                    = pprint' adapt reserved pat <+> equals <+> pprint' adapt reserved term

    pprint' adapt reserved (Isa.ListComp body stmts)
        = brackets $ pprint' adapt reserved body <+> text "." <+>
                       (vcat (punctuate comma (map ppStmt stmts)))
        where
          ppStmt (Isa.Guard b)
              = pprint' adapt reserved b
          ppStmt (Isa.Generator (p, e)) 
              = pprint' adapt reserved p <+> text "<-" <+> pprint' adapt reserved e

    pprint' adapt reserved (Isa.DoBlock pre stmts post) = 
        text pre <+> (vcat $ (printStmts stmts) ++ [text post])
        where printStmts [stmt] = [pprint' adapt reserved stmt]
              printStmts (stmt:stmts) = (pprint' adapt reserved stmt <> semi) : (printStmts stmts)

instance Printer Isa.Stmt where
    pprint' adapt reserved (Isa.DoGenerator pat exp) = pprint' adapt reserved pat <+> text "<-" <+> pprint' adapt reserved exp
    pprint' adapt reserved (Isa.DoQualifier exp) = pprint' adapt reserved exp


reAdaptEnvName :: AdaptionTable -> Env.EnvName -> Maybe Env.EnvName
reAdaptEnvName adapt name
    = let AdaptionTable mappings = adapt
          mappings' = [ (Env.identifier2name id2, Env.identifier2name id1) 
                            | (id1, id2) <- mappings ]
      in lookup name mappings'

isNil, isCons, isPairCon :: AdaptionTable -> Isa.Name -> Bool

mk_isFoo adapt foo n = case reAdaptEnvName adapt (Env.fromIsa n) of
  Nothing -> False
  Just x -> case Env.toHsk x of
    Special con -> con == foo
    _ -> False

isNil adapt = mk_isFoo adapt Hsx.ListCon
isCons adapt = mk_isFoo adapt Hsx.Cons
isPairCon adapt = mk_isFoo adapt (Hsx.TupleCon 2)

isEmptySig (Isa.TypeSig _ Isa.TyNone) = True
isEmptySig _ = False

pprintAsList :: AdaptionTable -> [String] -> [Isa.Term] -> DocM P.Doc
pprintAsList adapt reserved list = let
  (xs, [Isa.Var nil]) = splitAt (length list - 1) list
  in assert (isNil adapt nil)
    $ brackets (hsep (punctuate comma (map (pprint' adapt reserved) xs)))

pprintAsTuple :: AdaptionTable -> [String] -> [Isa.Term] -> DocM P.Doc
pprintAsTuple adapt reserved = parens . hsep . punctuate comma . map (pprint' adapt reserved)


data AppFlavor = ListApp [Isa.Term] 
               | TupleApp [Isa.Term] 
               | InfixApp Isa.Term Isa.Term Isa.Term 
               | UnaryOpApp
               | FunApp
  deriving (Show)

-- This makes use of pattern guards which are not Haskell98, but quite
-- portable across implementations nontheless.
--
-- Cf. http://www.haskell.org/ghc/docs/latest/html/users_guide/syntax-extns.html#pattern-guards
--

categorizeApp :: AdaptionTable -> Isa.Term -> (Isa.Name -> Maybe Env.Identifier) -> AppFlavor
categorizeApp adapt app@(Isa.App (Isa.App (Isa.Var opN) t1) t2) lookupFn
    | isCons adapt opN,    Just list <- flattenListApp adapt app  = ListApp list
    | isPairCon adapt opN, Just list <- flattenTupleApp adapt app = TupleApp list
    | isInfixOp opN lookupFn                          = InfixApp t1 (Isa.Var opN) t2
categorizeApp _ (Isa.App (Isa.Var opN) _) lookupFn
    | isUnaryOp opN lookupFn                              = UnaryOpApp
    | otherwise                                           = FunApp
categorizeApp _ _ _ = FunApp

flattenListApp :: AdaptionTable -> Isa.Term -> Maybe [Isa.Term]
flattenListApp adapt app = let
  list = unfoldr1 split app
  in case last list of -- proper list?
    (Isa.Var c) | isNil adapt c -> Just list
    _ -> Nothing
  where
    split (Isa.App (Isa.App (Isa.Var c) x) xs) | isCons adapt c = Just (x, xs)
    split _ = Nothing

flattenTupleApp :: AdaptionTable -> Isa.Term -> Maybe [Isa.Term]
flattenTupleApp adapt app = let list = unfoldr1 split app in
                      if (length list) > 1 then Just list
                                           else Nothing
  where
    split (Isa.App (Isa.App (Isa.Var c) x) xs) | isPairCon adapt c = Just (x, xs)
    split _ = Nothing

-- flattenLambdas ``%x . %y . %z . foo'' => ([x,y,z], foo)
--
flattenLambdas :: Isa.Term -> ([Isa.Name], Isa.Term)
flattenLambdas (Isa.Lambda arg1 (Isa.Lambda arg2 body)) 
    = let (args, real_body) = flattenLambdas body
      in ([arg1,arg2]++args, real_body)
flattenLambdas (Isa.Lambda arg body) = ([arg], body)
flattenLambdas t = ([], t)

isSelfEvaluating :: AdaptionTable -> Isa.Term -> (Isa.Name -> Maybe Env.Identifier) -> Bool
isSelfEvaluating adapt t lookupFn
    = case t of
        Isa.Var _            -> True
        Isa.Literal _        -> True
        Isa.Parenthesized _  -> True
        Isa.App _ _          -> case categorizeApp adapt t lookupFn of
                                  ListApp  _     -> True
                                  TupleApp _     -> True
                                  FunApp         -> False
                                  UnaryOpApp     -> False
                                  InfixApp _ _ _ -> False
        _ -> False

isCompound :: AdaptionTable -> Isa.Term -> (Isa.Name -> Maybe Env.Identifier) -> Bool
isCompound adapt t lookupFn
    = case t of
        Isa.Var _            -> False
        Isa.Literal _        -> False
        Isa.Parenthesized _  -> False
        Isa.App _ _          -> case categorizeApp adapt t lookupFn of
                                  ListApp  _     -> False
                                  TupleApp _     -> False
                                  FunApp         -> False
                                  UnaryOpApp     -> True
                                  InfixApp _ _ _ -> True
        _ -> True

isCompoundType :: Isa.Type -> Bool
isCompoundType t = case t of
                     Isa.TyVar _    -> False
                     Isa.TyCon _ [] -> False
                     _              -> True
                     
isInfixOp :: Isa.Name -> (Isa.Name -> Maybe Env.Identifier) -> Bool                 
isInfixOp name lookupFn
    = case lookupFn name of
        Just id -> Env.isInfixOp id
        _       -> False

isUnaryOp :: Isa.Name -> (Isa.Name -> Maybe Env.Identifier) -> Bool
isUnaryOp name lookupFn
    = case lookupFn name of
        Just id -> Env.isUnaryOp id
        _       -> False

lookupIdentifier :: Isa.Theory -> Isa.Name -> Env.GlobalE -> Maybe Env.Identifier
lookupIdentifier thy n globalEnv
    = Env.lookupConstant (Env.fromIsa thy) (Env.fromIsa n) globalEnv
