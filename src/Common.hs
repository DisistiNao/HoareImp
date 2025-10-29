{-# LANGUAGE CPP #-}
module Common where

import PrettyPrinter

#ifdef __HUGS__
import Control.Monad.Instances
#endif

allSame :: Eq a => [a] -> Bool
allSame []  = False
allSame [x] = True
allSame xs  = all (== head xs) (tail xs)

{- Position data structure, for applyXRule -}
data Pos = GoLeft | GoRight deriving (Eq, Show)
type Path = [Pos]

{- Proof data structure -}
-- Don't use this constructor directly. You should only construct proofs given the rules.
newtype Proof a = Proof a deriving (Eq, Show)

fromProof :: Proof a -> a
fromProof (Proof a) = a

instance (Show a, Pretty b) => Pretty (Either a b) where
  prPrec x (Right a) = prPrec x a
  prPrec x (Left a)  = (read (show a) :: String)

instance Pretty a => Pretty (Proof a) where
  prPrec x (Proof a) = "⊢ " ++ prPrec x a

#ifdef __HUGS__
(<$>) :: Functor f => (a -> b) -> f a -> f b
(<$>) = fmap

class (Functor f) => Applicative f where
  pure  :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

instance Applicative (Either e) where
  pure          = Right
  Left  e <*> _ = Left e
  Right f <*> r = fmap f r

instance Monad (Either e) where
  Left  l >>= _ = Left l
  Right r >>= k = k r
  return        = Right
#endif
