module Monads
    ( module Control.Monad.State,
      module Monads)
where

import Control.Monad.State


type MyState = Int
type MyStateM a = State MyState a