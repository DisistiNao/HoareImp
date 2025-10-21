module Gentzen where

import Common
import PrettyPrinter

{- Data defs -}

data PropCalc a =
  PropVar a
  | Not (PropCalc a)
  | And (PropCalc a) (PropCalc a)
  | Or (PropCalc a) (PropCalc a)
  | Imp (PropCalc a) (PropCalc a)
  deriving (Eq, Show)

type ESP a = Either String (Proof (PropCalc a))

instance Pretty a => Pretty (PropCalc a) where
  prPrec x (PropVar a) = prPrec x a
  prPrec q (Not formula) = prParen (q > 3) ("<",">") $
    "¬" ++ prPrec 3 formula
  prPrec q (And lhs rhs) = prParen (q > 2) ("<",">") $
    prPrec 3 lhs ++ "∧" ++ prPrec 2 rhs
  prPrec q (Or lhs rhs)  = prParen (q > 1) ("<",">") $
    prPrec 2 lhs ++ "∨" ++ prPrec 1 rhs
  prPrec q (Imp lhs rhs) = prParen (q > 0) ("<",">") $
    prPrec 1 lhs ++ "→" ++ prPrec 0 rhs

{- Helper functions -}

-- | Apply prop rule to a specific portion of a formula
-- Might be useful for some rules that may require drilling
applyPropRule :: Path -> (Proof (PropCalc a) -> ESP a) -> Proof (PropCalc a) -> ESP a
applyPropRule xs f (Proof x) = go xs f x
  where
  go :: Path -> (Proof (PropCalc a) -> ESP a) -> PropCalc a -> ESP a
  go (_:xs) f (Not x)         = go xs f x >>= \(Proof x) -> Right $ Proof $ Not x
  go (GoLeft:xs) f (And x y)  = go xs f x >>= \(Proof x) -> Right $ Proof $ And x y
  go (GoLeft:xs) f (Or x y)   = go xs f x >>= \(Proof x) -> Right $ Proof $ Or x y
  go (GoLeft:xs) f (Imp x y)  = go xs f x >>= \(Proof x) -> Right $ Proof $ Imp x y
  go (GoRight:xs) f (And x y) = go xs f y >>= \(Proof y) -> Right $ Proof $ And x y
  go (GoRight:xs) f (Or x y)  = go xs f y >>= \(Proof y) -> Right $ Proof $ Or x y
  go (GoRight:xs) f (Imp x y) = go xs f y >>= \(Proof y) -> Right $ Proof $ Imp x y
  go _ f x = f (Proof x)

{- Rules -}

-- | Joining Rule
-- If x and y are theorems, then <x∧y> is a theorem.
ruleJoin :: Proof (PropCalc a) -> Proof (PropCalc a) -> ESP a
ruleJoin (Proof x) (Proof y) = Right $ Proof $ And x y

-- | Sep Rule
-- If <x∧y> is a theorem, then both x and y are theorems.
ruleSepL :: Proof (PropCalc a) -> ESP a
ruleSepL (Proof (And x y)) = Right $ Proof x
ruleSepL _ = Left "ruleSepL: Cannot construct proof"

-- | Sep Rule
-- If <x∧y> is a theorem, then both x and y are theorems.
ruleSepR :: Proof (PropCalc a) -> ESP a
ruleSepR (Proof (And x y)) = Right $ Proof y
ruleSepR _ = Left "ruleSepL: Cannot construct proof"

-- | Double-Tilde Rule
-- The string ¬¬ can be deleted from any theorem. It can also be inserted into any theorem, provided that the resulting string is itself well-formed
ruleDoubleTildeIntro :: Proof (PropCalc a) -> ESP a
ruleDoubleTildeIntro (Proof x) = Right $ Proof $ Not (Not x)

-- | Double-Tilde Rule
-- The string ¬¬ can be deleted from any theorem. It can also be inserted into any theorem, provided that the resulting string is itself well-formed
ruleDoubleTildeElim :: Proof (PropCalc a) -> ESP a
ruleDoubleTildeElim (Proof (Not (Not x))) = Right $ Proof x
ruleDoubleTildeElim _ = Left "ruleDoubleTildeElim: Cannot construct proof"

-- | Fantasy Rule (Carry over)
-- If x were a theorem, y would be a theorem.
-- Additionally, inside a fantasy, any theorem from the "reality" one level higher can be brought in and used.
-- Imp intro accepts a rule and an assumption (simply a well-formed formula, not necessarily proven)
-- Our data types are constructed such that all formulas are well-formed
ruleFantasy :: PropCalc a -> (Proof (PropCalc a) -> ESP a) -> ESP a
ruleFantasy x f = f (Proof x) >>= \(Proof y) -> Right $ Proof $ Imp x y

-- | Rule of Detachment
-- If x and <x⊃y> are both theorems, then y is a theorem.
ruleDetachment :: Eq a => Proof (PropCalc a) -> Proof (PropCalc a) -> ESP a
ruleDetachment (Proof x) (Proof (Imp x' y)) | x == x' = Right $ Proof y
ruleDetachment _ _ = Left "ruleDetachment: Cannot construct proof"

-- | Contrapositive Rule
-- <x⊃y> and <¬y⊃¬x> are interchangeable.
ruleContra :: Proof (PropCalc a) -> ESP a
ruleContra (Proof (Imp (Not y) (Not x))) = Right $ Proof $ Imp x y
ruleContra (Proof (Imp x y)) = Right $ Proof $ Imp (Not y) (Not x)
ruleContra _ = Left "ruleContra: Cannot construct proof"

-- | De Morgan's Rule
-- <¬x∧¬y> and ¬<x∨y> are interchangeable.
ruleDeMorgan :: Proof (PropCalc a) -> ESP a
ruleDeMorgan (Proof (And (Not x) (Not y))) = Right $ Proof $ Not (Or x y)
ruleDeMorgan (Proof (Not (Or x y))) = Right $ Proof $ And (Not x) (Not y)
ruleDeMorgan _ = Left "ruleDeMorgan: Cannot construct proof"

-- | Switcheroo Rule
-- <x∨y> and <¬x⊃y> are interchangeable.
ruleSwitcheroo :: Proof (PropCalc a) -> ESP a
ruleSwitcheroo (Proof (Or x y)) = Right $ Proof $ Imp (Not x) y
ruleSwitcheroo (Proof (Imp (Not x) y)) = Right $ Proof $ Or x y
ruleSwitcheroo _ = Left "ruleSwitcheroo: Cannot construct proof"
