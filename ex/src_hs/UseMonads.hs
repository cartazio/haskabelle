module UseMonads
where
import Monads

addState :: Int -> MyStateM Int
addState n = do cur <- get
                let new = (cur + n)
                put new
                return new


addStateE :: Int -> MyErrorM Int
addStateE n = 
    do cur <- lift get
       let new = cur + n
       when (new < 0) $
            throwError "state must not be negative"
       lift $ put new
       return new