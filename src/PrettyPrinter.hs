module PrettyPrinter where

{- Pretty printer -}
class Pretty a where
  prPrec :: Int -> a -> String

pr :: Pretty a => a -> String
pr = prPrec 0

prParen :: Bool -> (String, String) -> String -> String
prParen b (open, close) p = if b then open ++ p ++ close else p

instance Pretty Integer where
  prPrec _ = show

instance Pretty Bool where
  prPrec _ = show
