module Monads
    ( module Control.Monad.State,
      module Monads)
where

import Control.Monad.State
import Control.Monad.Error


type MyState = Int
type MyError = String

type MyStateM = State MyState

type MyErrorM= ErrorT MyError MyStateM