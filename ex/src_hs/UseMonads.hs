module UseMonads
where
import Monads

addState :: Int -> MyStateM Int
addState n = do cur <- get
                let new = (cur + n)
                put new
                return new