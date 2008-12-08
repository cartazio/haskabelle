module UseMonads
where
import Monads

addState :: Int -> StateM Int
addState n = do cur <- get
                let new = (cur + n)
                put new
                return new


addState' :: Int -> ErrorM Int
addState' n = 
    do new <- lift (do cur <- get
                       let new = cur + n
                       put new
                       return new)
       when (new < 0) $
            throwError "state must not be negative"
       return new