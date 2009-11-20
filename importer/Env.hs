{-# LANGUAGE
  UndecidableInstances,
  ExistentialQuantification,
  MultiParamTypeClasses, 
  RankNTypes, 
  FlexibleInstances #-}

{-| Author: Patrick Bahr, NICTA

This module provides traversal schemes for SYB that enable access to
modular defined environment information.
-}

module Importer.Env
    ( EnvDef,
      everywhereEnv,
      everythingEnv,
      mkE,
      extE,
      liftE,
      extByC,
      uniEloc,
      Envs(..),
      Repl(..)
    )
where

import Data.Generics
import Data.Monoid
import Control.Monad
import Control.Monad.Reader

class Component t c where
    extract :: t -> c
    liftC :: (c -> c) -> (t -> t)

instance Component (a, b) a where
    extract (a,b) = a
    liftC f (a,b) = (f a,b)

instance Component (a, b) b where
    extract (a,b) = b
    liftC f (a,b) = (a,f b)

{-|
  Elements of this type define how environments of type @e@ are changed
  during the generic traversal of a data structure.
-}
newtype EnvDef m e = EnvDef (forall a. Data a => a -> m [e -> e])
data Envs e = Envs [e]
data Repl e = Set e | Keep

{-|
  This function turns a simple query function into a function
  that returns a list repeating the original result as often as
  there are immediate subterms in the argument.
-}
uniE :: (Monad m, Data a) => (a -> m b) -> (a -> m (Envs b))
uniE query node =
    do res <- query node
       return $ Envs $ replicate (glength node) res

{-|
  This function is similar to 'uniE' but it can be used locally, i.e.,
  in the definition of a particular environment transformation function.
  It returns a list repeating second argument as often as
  there are immediate subterms in first argument value the argument.
-}
uniEloc :: (Data a) => a -> b -> Envs b
uniEloc node env = Envs $ replicate (glength node) env

{-|
  This function turns pure environment transformation into monadic ones.
-}
pureE :: Monad m => (a -> e) -> (a -> m e)
pureE pure node = return (pure node)

{-|
  This function turns constant environment transformations into environment
  transformations that accumulate the environment values.
-}
accE :: (Monad m, Monoid e) => (a -> m (Envs e)) -> (a -> m (Envs (e -> e)))
accE accum node =
    do Envs res <- accum node 
       return $ Envs $ map (flip mappend) res

{-|
  This function turns constant environment transformations into environment
  transformations that replace the current environment with a new
  value (for @Set@) or keep it (for @Keep@)
-}
replE :: (Monad m) => (a -> m (Envs (Repl e))) -> (a -> m (Envs (e -> e)))
replE repl node =
    do Envs res <- repl node
       return $ Envs $ map replMb res
    where replMb Keep    old = old
          replMb (Set new) _   = new

{-|
  This environment definition will result in no changes to
  the environment during the generic traversal.
-}

nilE :: (Monad m) => EnvDef m e
nilE = EnvDef (return . flip replicate id. glength)

{-|
  This function constructs an environment definition from
  a function that produces an transformation for a specific
  type @a@. The environment transformations from the list are applied to the respective immediate
  subterm of the data type @a@, i.e., the first element is applied to the first component
  of the type etc. For all other types the environment is left unchanged.
-}
mkE :: (EnvFunction b e, Monad m, Data a) => (a -> b) ->  EnvDef m e
mkE = extE nilE

{-|
  This function constructs an environment definition from
  a monadic function that produces an environment transformation for a specific
  type @a@. The environment transformations from the list are applied to the respective immediate
  subterm of the data type @a@, i.e., the first element is applied to the first component
  of the type etc. For all other types the environment is left unchanged.
-}
mkEm :: (EnvFunction b e, Monad m, Data a) => (a -> m b) ->  EnvDef m e
mkEm =  extEm nilE


{-|
  This function extends the given base environment definition by
  a function that produces an environment transformation for a specific
  type @a@. The environment transformations from the list are applied to the respective
  successor of the data type @a@, i.e., the first element is applied to the first component
  of the type etc. For all other types the environment is transformed as by the
  base transformer that was given to this function.
-}

extE :: (EnvFunction b e, Monad m, Data a) => EnvDef m e -> (a -> b) ->  EnvDef m e
extE base trans = extEm base (pureE trans)

{-|
  This function extends the given base environment definition by
  a monadic function that produces an environment transformation for a specific
  type @a@. The environment transformations from the list are applied to the respective
  successor of the data type @a@, i.e., the first element is applied to the first component
  of the type etc. For all other types the environment is transformed as by the
  base transformer that was given to this function.
-}

extEm :: (EnvFunction b e, Monad m, Data a) => EnvDef m e -> (a -> m b) ->  EnvDef m e
extEm (EnvDef base) trans = EnvDef ( base `extQ` ext)
    where ext node = do Envs res <- toEnvFunction trans node
                        return res



class EnvFunction b e where
    toEnvFunction :: (Monad m, Data a) => (a -> m b) -> (a -> m (Envs (e -> e)))

instance EnvFunction (Envs(e -> e)) e where
    toEnvFunction = id

instance EnvFunction (e -> e) e where
    toEnvFunction = uniE

instance EnvFunction (Envs( Repl e)) e where
    toEnvFunction = replE

instance EnvFunction (Repl e) e where
    toEnvFunction = replE . uniE

instance (Monoid e) => EnvFunction (Envs e) e where
    toEnvFunction = accE

instance (Monoid e) => EnvFunction e e where
    toEnvFunction = accE . uniE


{-|
  This function takes a transformer for environments of type @c@ and
  lifts it to a corresponding transformer for environments of type @e@
  that has @c@ as a component. The resulting transformer only acts on the
  @c@ component of @e@.
-}

liftE :: (Monad m, Component e c) => EnvDef m c -> EnvDef m e
liftE (EnvDef query) = (EnvDef query')
    where query' node =
              do res <- query node
                 return $ map liftC res

{-|
  This function extends a transformer for environments of type @e@
  by a transformer for environments of type @c@ which is a component
  of $e$. 
-}

extByC :: (Monad m, Component e c) => EnvDef m e -> EnvDef m c -> EnvDef m e
extByC (EnvDef base) (EnvDef ext) = (EnvDef query)
    where query node =
              do extRes <- ext node
                 baseRes <-base node
                 return $ zipWith (.) baseRes (map liftC extRes)


{-|
  This function applies the given monadic transformation function everywhere
  in a bottom-up manner and provides environment information during the traversal
  as generated by the given environment transformer.
-}
everywhereEnv :: MonadReader e m =>
                 EnvDef m e -> GenericM m -> GenericM m
everywhereEnv envDef@(EnvDef envTrans) f node = 
    do trans <- envTrans node
       node' <- gmapEnvT trans (everywhereEnv envDef f) node
       f node'

{-|
  This function summarises the queried results collected by
  a traversal and provides environment information during the traversal
  as generated by the given environment transformer.
-}

everythingEnv :: MonadReader e m =>
                 EnvDef m e -> (q -> q -> q) -> GenericQ (m q) -> GenericQ (m q)
everythingEnv envDef@(EnvDef envTrans) combine f node =
    do trans <- envTrans node
       children <- gmapEnvQ trans (everythingEnv envDef combine f) node
       current <- f node
       return $ foldl combine current children
        
{-|
  This function checks that the given node has the same number of immediate subterms as
  there are elements in the list. If so the last argument is returned. Otherwise an 
  exception is thrown.  
-}
checkTrans :: Data a => a -> [r -> r] -> b -> b
checkTrans node trans x
    | children > ts = error $ "Too few environment transformations for constructor \""
                               ++ show (toConstr node) ++ "\": Expected "
                                      ++ show children ++ ", but found " ++ show ts
    | children < ts = error $ "Too many environment transformations for constructor \""
                               ++ show (toConstr node) ++ "\": Expected "
                                      ++ show children ++ ", but found " ++ show ts
    | otherwise = x
                   
    where children = glength node
          ts = length trans

{-|
  A type definition needed to define 'gmapEnvT'.
-}
newtype EnvT  m a r = EnvT (m ([a -> a],r))
unEnvT (EnvT x) = x

{-|
  This function applies the given monadic transformer to all immediate 
  subterms. The environments of the resulting monadic computations are
  modified as given by the list of environment transformation functions, where 
  the i-th function in the list is used for the i-th subterm.
-}
gmapEnvT ::MonadReader r m => [r -> r] -> GenericM m -> GenericM m
gmapEnvT trans f node = checkTrans node trans $
                        unEnvT (gfoldl k z node) >>= (return . snd)
    where z x = EnvT $ return (trans,x)
          k (EnvT c) x = EnvT $
                       do (t:ts,c') <- c
                          x' <- local t (f x)
                          return (ts, c' x')

{-|
  This function applies the given monadic query to all immediate 
  subterms. The environments of the resulting monadic computations are
  modified as given by the list of environment transformation functions, where 
  the i-th function in the list is used for the i-th subterm.
-}
gmapEnvQ :: MonadReader r m => [r -> r] -> GenericQ (m q) -> GenericQ (m [q])
gmapEnvQ trans f node = checkTrans node trans $
                        sequence $ zipWith local trans (gmapQ f node)