module ExampleCommon where

import PrettyPrinter

{- Example variables -}
data Vars = A | B | C | D | E deriving (Eq, Ord, Show)

instance Pretty Vars where
  prPrec _ = show
