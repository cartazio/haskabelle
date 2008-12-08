module Monads
    (module Monads,
     module Control.Monad)
where

import Control.Monad

newtype StateM a = StateM ( Int -> (a,Int) )

instance Monad StateM where
    (StateM f') >>= g = StateM (\s -> let (r,s') = f' s
                                          StateM g' = g r
                                      in g' s')
    return v = StateM (\s -> (v,s))

put :: Int -> StateM ()
put state = StateM (\_ -> ((),state))

get :: StateM Int
get = StateM (\s -> (s,s))

newtype ErrorM a = ErrorM (StateM (Either String  a))

instance Monad ErrorM where
    (ErrorM f') >>= g = ErrorM comb
        where comb = do r <- f'
                        case r of
                          Left e -> return (Left e)
                          Right v -> let ErrorM g' = g v
                                     in g'
    return v = ErrorM (return (Right v))

lift :: StateM a -> ErrorM a
lift sm = ErrorM (sm >>= (return . Right))


throwError :: String -> ErrorM a
throwError e = ErrorM (return (Left e))
