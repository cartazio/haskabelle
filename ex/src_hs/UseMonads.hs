module UseMonads
where
import Monads

addState :: Int -> MyStateM Int
addState n = do cur <- get
                let new = (cur + n)
                put new
                return new


addStateE' :: Int -> MyErrorM Int
addStateE' n = lift $ do x <- get
                         put x
                         return x

 
addStateE :: Int -> MyErrorM Int
addStateE n = do cur <- lift $
                       do x <- get
                          put x
                          return x
                 let new = (cur + n)
                 lift $ put new
                 return ()
                 return new

doNothing :: MyErrorM ()
doNothing = return ()