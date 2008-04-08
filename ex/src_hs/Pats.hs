module Pats where

--import Chalmers.QuickCheck
import Text.PrettyPrint.HughesPJ
import Base
import Cover

-- Signatures
type Sort = Int
type FSym = Int

type Sig = [ (String, [ (String, [Sort] ) ]) ]

-- Terms
data Pat = Blank Sort 
         | Cons Sort FSym [ Pat ]
 deriving (Eq, Show, Read)

-- Matching

matches _  (Blank _) = True
matches (Blank _) (Cons _ _ _) = False
matches (Cons _ i ps) (Cons _ j qs)  = i == j && and (zipWith matches ps qs)

-- Ord instance (Only required for Data.*)

instance Ord Pat where
  (Blank _) <= _            = True
  (Cons _ _ _) <= (Blank _) = False
  (Cons s f ps) <= (Cons t g qs) = (f < g) || (f <= g && ps <= qs)

  p < q       = (p <= q) && (p /= q)
  p >= q      = q <= p
  p > q       = q < p

-- Sort of a term
sort :: Pat -> Sort

sort (Blank s) = s
sort (Cons s _ _) = s

-- Signature operations

constrs :: Sig -> Sort -> [ (String, [ Sort ]) ]
constrs sig s = snd (sig !! s)

args :: Sig -> Sort -> FSym -> [Sort]
args sig s c = snd (constrs sig s !! c)

cname :: Sig -> Sort -> FSym -> String
cname sig s c = fst (constrs sig s !! c)

-- Pretty Printing using a signature
pp_term sig (Blank _) = text "_"
pp_term sig (Cons s f ts) = text (cname sig s f)
                            <> if null ts then empty 
                               else parens (cat $ punctuate comma (map (pp_term sig) ts))

-- Wellformedness
wellformed :: Sig -> Pat -> Bool

wellformed sig (Blank _) = True
wellformed sig (Cons s f ps) = 
    s < length sig
    && f < length (constrs sig s)
    && (args sig s f == map sort ps)
    && all (wellformed sig) ps
               

-- Ground term
ground (Blank _) = False
ground (Cons s f ps) = all ground ps

-- Supremum
sup (Blank s) _ = Blank s
sup _ (Blank s) = Blank s
sup (Cons s f ps) (Cons _ g qs)
    | f == g    = Cons s f (zipWith sup ps qs)
    | otherwise = Blank s
    
ovlp :: Pat -> Pat -> Bool
-- Optimized for zero-space behaviour. This doesnt seem to save time, though...
ovlp (Blank _) p = True
ovlp p (Blank _) = True
ovlp (Cons s f ps) (Cons _ g qs)
    | f == g    = allovlp ps qs -- and $ zipWith ovlp ps qs 
    | otherwise = False
  where allovlp [] [] = True
        allovlp (p:ps) (q:qs) 
            | ovlp p q  = allovlp ps qs
            | otherwise = False

------ QuickCheck setup

-- generate wellformed patterns
{-genpat :: Sig -> Sort -> Gen Pat
genpat sig s = sized (\n -> gen n s)
    where
      gen 0 s = return (Blank s)
      gen n s = do f <- choose (0, length cs - 1)
                   ps <- mapM (gen (n - 1)) (snd (cs !! f))
                   return (Cons s f ps)
                where cs = constrs sig s
       
prop_wf_genpat :: Sig -> Sort -> Property
prop_wf_genpat sig s = forAll (genpat sig s) $ \p -> wellformed sig p
-}

-- Projections of a list of patterns

is_wc :: Pat -> Bool

is_wc (Blank _) = True
is_wc (Cons _ _ _) = False


is_cons :: FSym -> Pat -> Bool

is_cons i (Cons _ j _) | i == j = True 
is_cons _ _ = False


proj_cons :: Int -> Pat -> Pat

proj_cons i (Cons _ _ ts) = ts !! i



proj :: Sig -> FSym -> Int -> [ Pat ] -> [ Pat ]

proj sig c i [] = []
proj sig c i ps | any is_wc ps = distinct (Blank subs : prs)
                | otherwise = distinct prs
    where s = sort (head ps)
          subs = args sig s c !! i
          prs = [ proj_cons i p |  p <- ps, is_cons c p] 

constructors sig s = zip [0 .. length cs - 1] cs
    where cs = map snd (constrs sig s)



-- Minterms
minterms :: Sig -> [ Pat ] -> [ Pat ]

minterms sig [] = []
minterms sig ps | all is_wc ps = [Blank s]
          | otherwise    = 
              concat [ map (Cons s i) $ cprod (subs i (length ts)) | 
                       (i, ts) <- constructors sig s ]
          where s = sort (head ps)
                subs :: Int -> Int -> [[ Pat ]]
                subs c n = map (\i -> minterms sig $ proj sig c i ps) [0 .. n - 1]
                                       
-- Prime implicants
prime_imp' inT cov unc =
    sups matches (filter inT ([ sup m m' | (m,m') <- unordered_pairs unc ] 
                              ++ [ sup m m' | m <- unc, m' <- cov ]))

prime_imp inT ms = prime_imp' inT [] ms

list_ctxts f xs = lc id xs
    where lc c [] = []
          lc c (x:xs) = f c x xs : lc (c . (x:)) xs

pat_ctxts :: Pat -> [(Pat, Pat -> Pat)]
pat_ctxts (Cons s f ps) = list_ctxts (\c x ys -> (x, (\z -> Cons s f (c (z : ys))))) ps

ncube inT p = nc' id p
    where nc' c (Blank s) = (Blank s)
          nc' c (cns @ (Cons s f ps)) =
              if inT (c (Blank s)) then Blank s
              else Cons s f [ nc' (c . c') p | (p, c') <- pat_ctxts cns ]


-- essential prime implicants (FIXME: distinct -> Data.Set ???)
essential_pis inT ms = distinct [ r | m <- ms, r <- [ncube inT m], inT r]


-- make a list of patterns disjoint

group_minterms ps ms =
    fst (fold_map step ps ([], ms))
    where step p (done, rest) = 
              let (pos, neg) = pos_neg_filter (`matches` p) rest
              in ((pos, done ++ neg), (done ++ pos, neg))

bench (sig, ps) =
    let
        ms = minterms sig ps
        as = group_minterms ps ms
        cfun = matrix_stepwise_cover
        cover (pos, neg) = 
            let inT m = not (any (ovlp m) neg)
                es = essential_pis inT pos
                (cov, unc) = pos_neg_filter (\m -> any (m `matches`) es) pos
                pis' = prime_imp' inT cov unc
                cpis = cfun (\p m -> m `matches` p) pis' unc
                res = es ++ cpis
            in
              (length es, length pis', length cpis)
                      
        sstats = foldr (\(e,pis,cpis) (e',pis',cpis') -> (e+e', pis+pis', cpis+cpis')) (0, 0, 0) 
                 $ map cover as
    in
      (length ps, length ms, sstats)

bench2 (sig, ps) =
    let
        ms = minterms sig ps
        as = group_minterms ps ms
        cfun = matrix_stepwise_cover
        cover (pos, neg) = 
            let inT m = not (any (ovlp m) neg)
                es = essential_pis inT pos
                (cov, unc) = pos_neg_filter (\m -> any (m `matches`) es) pos
                pis' = prime_imp' inT cov unc
                cpis = cfun (\p m -> m `matches` p) pis' unc
                res = es ++ cpis
            in
              res
    in
      map cover as
