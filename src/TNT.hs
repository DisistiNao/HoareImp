module TNT
  (Arith(..)
  , FOL(..)
  , applyFOLRule
  , axiom1
  , axiom2
  , axiom3
  , axiom4
  , axiom5
  , substPropCalc
  , ruleAddS
  , ruleDropS
  , ruleExistence
  , ruleGeneralize
  , ruleInduction
  , ruleInterchangeL
  , ruleInterchangeR
  , ruleSpec
  , ruleSymmetry
  , ruleTransitivity
  ) where

import Common
import Data.List ((\\), nub)
import Gentzen
import PrettyPrinter

{- Data defs -}

data Arith a =
  Var a
  | Z
  | S (Arith a)
  | Plus (Arith a) (Arith a)
  | Mult (Arith a) (Arith a)
  deriving (Eq, Show)

data FOL a =
  Eq (Arith a) (Arith a)
  | ForAll a (PropCalc (FOL a))
  | Exists a (PropCalc (FOL a))
  deriving (Eq, Show)

instance Pretty a => Pretty (Arith a) where
  prPrec q (Var a)     = prPrec q a
  prPrec q Z           = "0"
  prPrec q (Plus a b)  = prParen (q > 5) ("(",")") $ prPrec 6 a ++ "+" ++ prPrec 5 b
  prPrec q (Mult a b)  = prParen (q > 6) ("(",")") $ prPrec 7 a ++ "*" ++ prPrec 6 b
  prPrec q (S a)       = prParen (q > 7) ("(",")") $ "S" ++ prPrec 7 a

instance Pretty a => Pretty (FOL a) where
  prPrec q (Eq a b)     = prParen (q > 4) ("(",")") $ prPrec 5 a ++ "=" ++ prPrec 4 b
  prPrec q (ForAll x y) = prParen (q > 8) ("(",")") $ "∀" ++ prPrec 9 x ++ ":" ++ prPrec 8 y
  prPrec q (Exists x y) = prParen (q > 9) ("(",")") $ "∃" ++ prPrec 10 x ++ ":" ++ prPrec 9 y

{- Helper functions -}

-- | Apply FOL rule to a specific portion of a formula
-- Might be useful for some rules that may require drilling, like `ruleInterchangeL`
-- Restriction: Using `applyFOLRule` within `applyFOLRule` is not allowed on any variable which appeared bound in the context.
applyFOLRule :: Eq a => Path -> (Proof (PropCalc (FOL a)) -> ESP (FOL a)) -> [Proof (PropCalc (FOL a))] -> Proof (PropCalc (FOL a)) -> ESP (FOL a)
applyFOLRule xs f ctx (Proof x) = go xs f x [] ctx
  where
  go :: Eq a => Path -> (Proof (PropCalc (FOL a)) -> ESP (FOL a)) -> PropCalc (FOL a) -> [a] -> [Proof (PropCalc (FOL a))] -> ESP (FOL a)
  go [] f x boundVars premises | not (any (`elem` boundVars) (concatMap (getFreeVars . fromProof) premises)) = f (Proof x)
  go (_:xs) f (PropVar (ForAll x y)) boundVars ctx = go xs f y (x : boundVars) ctx >>= \(Proof y) -> Right $ Proof $ PropVar (ForAll x y)
  go (_:xs) f (PropVar (Exists x y)) boundVars ctx = go xs f y (x : boundVars) ctx >>= \(Proof y) -> Right $ Proof $ PropVar (Exists x y)
  go (_:xs) f (Not x) boundVars ctx                = go xs f x boundVars ctx >>= \(Proof x) -> Right $ Proof $ Not x
  go (GoLeft:xs) f (And x y) boundVars ctx         = go xs f x boundVars ctx >>= \(Proof x) -> Right $ Proof $ And x y
  go (GoLeft:xs) f (Imp x y) boundVars ctx         = go xs f x boundVars ctx >>= \(Proof x) -> Right $ Proof $ Imp x y
  go (GoLeft:xs) f (Or x y) boundVars ctx          = go xs f x boundVars ctx >>= \(Proof x) -> Right $ Proof $ Or x y
  go (GoRight:xs) f (And x y) boundVars ctx        = go xs f y boundVars ctx >>= \(Proof y) -> Right $ Proof $ And x y
  go (GoRight:xs) f (Imp x y) boundVars ctx        = go xs f y boundVars ctx >>= \(Proof y) -> Right $ Proof $ Imp x y
  go (GoRight:xs) f (Or x y) boundVars ctx         = go xs f y boundVars ctx >>= \(Proof y) -> Right $ Proof $ Or x y
  go _ _ _ _ _ = Left "applyFOLRule: Cannot apply rule"

-- Similar to applyFOLRule, but useful for terms within formulas (used by existence rule)
applyArithRule :: Path -> (Arith a -> Arith a) -> Arith a -> Arith a
applyArithRule [] f x = f x
applyArithRule (GoLeft:xs) f (S x) = S (applyArithRule xs f x)
applyArithRule (GoLeft:xs) f (Plus x y)  = Plus (applyArithRule xs f x) y
applyArithRule (GoLeft:xs) f (Mult x y)  = Mult (applyArithRule xs f x) y
applyArithRule (GoRight:xs) f (S x) = S (applyArithRule xs f x)
applyArithRule (GoRight:xs) f (Plus x y)  = Plus x (applyArithRule xs f y)
applyArithRule (GoRight:xs) f (Mult x y)  = Mult x (applyArithRule xs f y)
applyArithRule _ _ Z = Z -- nothing to apply for 0
applyArithRule _ _ (Var x) = Var x -- nothing to apply for a variable

-- Combines applyFOLRule and applyArithRule
applyFOLArithRule :: Eq a => Pos -> Path -> Path -> (Arith a -> Arith a) -> Proof (PropCalc (FOL a)) -> ESP (FOL a)
applyFOLArithRule pos path1 path2 f x = applyFOLRule path1 (\(Proof y) -> Right $ Proof $ go pos y) [] x
  where
  go GoLeft (PropVar (Eq x y)) = PropVar (Eq (applyArithRule path2 f x) y)
  go GoRight (PropVar (Eq x y)) = PropVar (Eq x (applyArithRule path2 f y))
  go _ x = x

-- Get FOL term, given specific path
getFOLTerm :: Path -> PropCalc (FOL a) -> PropCalc (FOL a)
getFOLTerm (_:xs) (PropVar (ForAll x y)) = getFOLTerm xs y
getFOLTerm (_:xs) (PropVar (Exists x y)) = getFOLTerm xs y
getFOLTerm (_:xs) (Not x)                = getFOLTerm xs x
getFOLTerm (GoLeft:xs) (And x y)         = getFOLTerm xs x
getFOLTerm (GoLeft:xs) (Imp x y)         = getFOLTerm xs x
getFOLTerm (GoLeft:xs) (Or x y)          = getFOLTerm xs x
getFOLTerm (GoRight:xs) (And x y)        = getFOLTerm xs y
getFOLTerm (GoRight:xs) (Imp x y)        = getFOLTerm xs y
getFOLTerm (GoRight:xs) (Or x y)         = getFOLTerm xs y
getFOLTerm _ x = x

-- Get Arith term, given specific position of equation and path
getArithTerm :: (Pos, Path) -> PropCalc (FOL a) -> Arith a
getArithTerm (pos, path) (PropVar (Eq x y)) = if pos == GoLeft then go path x else go path y
  where
  go :: Path -> Arith a -> Arith a
  go (GoLeft:xs) (S x)       = go xs x
  go (GoLeft:xs) (Plus x y)  = go xs x
  go (GoLeft:xs) (Mult x y)  = go xs x
  go (GoRight:xs) (S x)      = go xs x
  go (GoRight:xs) (Plus x y) = go xs y
  go (GoRight:xs) (Mult x y) = go xs y
  go _ x = x

-- Helper wrapper
getTerm :: (Pos, Path, Path) -> PropCalc (FOL a) -> Arith a
getTerm (pos, path1, path2) x = getArithTerm (pos, path2) (getFOLTerm path1 x)

-- Substitution function for arithmetical formulas
substArith :: Eq a => Arith a -> Arith a -> Arith a -> Arith a
substArith (S q) v e = S (substArith q v e)
substArith (Plus a b) v e = Plus (substArith a v e) (substArith b v e)
substArith (Mult a b) v e = Mult (substArith a v e) (substArith b v e)
substArith x v e | x == v = e
substArith x v e = x

-- Substitution on equational level for a specific expression with another expression
substPropCalc :: Eq a => Proof (PropCalc (FOL a)) -> Arith a -> Arith a -> Proof (PropCalc (FOL a))
substPropCalc (Proof f) v e = Proof $ go f v e
  where
  go :: Eq a => PropCalc (FOL a) -> Arith a -> Arith a -> PropCalc (FOL a)
  go (PropVar (Eq a b)) v e     = PropVar (Eq (substArith a v e) (substArith b v e))
  go (PropVar (ForAll x y)) v e = PropVar (ForAll x (go y v e))
  go (PropVar (Exists x y)) v e = PropVar (Exists x (go y v e))
  go (Not x) v e                = Not (go x v e)
  go (And x y) v e              = And (go x v e) (go y v e)
  go (Or x y) v e               = Or (go x v e) (go y v e)
  go (Imp x y) v e              = Imp (go x v e) (go y v e)

-- Find bound variables in a formula
getBoundVars :: Eq a => PropCalc (FOL a) -> [a]
getBoundVars x = nub $ go x
  where
  go (PropVar (ForAll x y)) = x : go y
  go (PropVar (Exists x y)) = x : go y
  go _ = []

-- Get all variables used in an arithmetic formula
getArithVars :: Eq a => Arith a -> [a]
getArithVars x = nub $ go x
  where
  go (Var a) = [a]
  go (S x) = go x
  go (Plus a b) = go a ++ go b
  go (Mult a b) = go a ++ go b
  go _ = []

-- Get all used variables
getVars :: Eq a => PropCalc (FOL a) -> [a]
getVars x = nub $ go x
  where
  go (PropVar (ForAll x y)) = go y
  go (PropVar (Exists x y)) = go y
  go (PropVar (Eq a b)) = getArithVars a ++ getArithVars b
  go (Not x) = go x
  go (And x y) = go x ++ go y
  go (Or x y) = go x ++ go y
  go (Imp x y) = go x ++ go y

-- Get all free variables
getFreeVars :: Eq a => PropCalc (FOL a) -> [a]
getFreeVars x = getVars x \\ getBoundVars x

{- Axioms -}

-- | Peano axiom 1: forall a, not (S a = 0)
axiom1 :: Arith a -> ESP (FOL a)
axiom1 (Var a) = Right $ Proof $ PropVar (ForAll a (Not (PropVar (Eq (S (Var a)) Z))))
axiom1 _ = Left "axiom1: Cannot construct proof"

-- | Peano axiom 2: forall a, (a + 0) = a
axiom2 :: Arith a -> ESP (FOL a)
axiom2 (Var a) = Right $ Proof $ PropVar (ForAll a (PropVar (Eq (Plus (Var a) Z) (Var a))))
axiom2 _ = Left "axiom2: Cannot construct proof"

-- | Peano axiom 3: forall a, forall b, a + Sb = S(a + b)
axiom3 :: Arith a -> Arith a -> ESP (FOL a)
axiom3 (Var a) (Var b) = Right $ Proof $ PropVar (ForAll a (PropVar (ForAll b (PropVar (Eq (Plus (Var a) (S (Var b))) (S (Plus (Var a) (Var b))))))))
axiom3 _ _ = Left "axiom3: Cannot construct proof"

-- | Peano axiom 4: forall a, (a * 0) = 0
axiom4 :: Arith a -> ESP (FOL a)
axiom4 (Var a) = Right $ Proof $ PropVar (ForAll a (PropVar (Eq (Mult (Var a) Z) Z)))
axiom4 _ = Left "axiom4: Cannot construct proof"

-- | Peano axiom 5: forall a, forall b, a * Sb = (a * b + a)
axiom5 :: Arith a -> Arith a -> ESP (FOL a)
axiom5 (Var a) (Var b) = Right $ Proof $ PropVar (ForAll a (PropVar (ForAll b (PropVar (Eq (Mult (Var a) (S (Var b))) (Plus (Mult (Var a) (Var b)) (Var a)))))))
axiom5 _ _ = Left "axiom5: Cannot construct proof"

{- Rules -}

-- | Rule of Specification
-- Suppose u is a variable which occurs inside the string x. If the string ∀u:x is a theorem, then so is x, and so are any strings made from x by replacing u, wherever it occurs, by one and the same term. (Restriction: The term which replaces u must not contain any variable that is quantified in x.)
ruleSpec :: Eq a => Arith a -> Proof (PropCalc (FOL a)) -> ESP (FOL a)
ruleSpec e (Proof (PropVar (ForAll x y))) | not (any (`elem` getArithVars e) (getBoundVars y)) = Right $ substPropCalc (Proof y) (Var x) e
ruleSpec _ _ = Left "ruleSpec: Cannot construct proof"

-- | Rule of Generalization
-- Suppose x is a theorem in which u, a variable, occurs free. Then ∀u:x is a theorem. (Restriction: No generalization is allowed in a fantasy on any variable which appeared free in the fantasy's premise.)
ruleGeneralize :: Eq a => a -> [Proof (PropCalc (FOL a))] -> Proof (PropCalc (FOL a)) -> ESP (FOL a)
ruleGeneralize x premises (Proof y) | x `notElem` getBoundVars y && x `notElem` concatMap (getFreeVars . fromProof) premises -- fantasy vars
  = Right $ Proof $ PropVar (ForAll x y)
ruleGeneralize _ _ _ = Left "ruleGeneralize: Cannot construct proof"

-- | Rule of Interchange
-- Suppose u is a variable. Then the strings ∀u:¬ and ¬∃u: are interchangeable anywhere inside any theorem.
ruleInterchangeL :: Proof (PropCalc (FOL a)) -> ESP (FOL a)
ruleInterchangeL (Proof (PropVar (ForAll x (Not y)))) = Right $ Proof $ Not (PropVar $ Exists x y)
ruleInterchangeL _ = Left "ruleInterchangeL: Cannot construct proof"

-- | Rule of Interchange
-- Suppose u is a variable. Then the strings ∀u:¬ and ¬∃u: are interchangeable anywhere inside any theorem.
ruleInterchangeR :: Proof (PropCalc (FOL a)) -> ESP (FOL a)
ruleInterchangeR (Proof (Not (PropVar (Exists x y)))) = Right $ Proof $ PropVar (ForAll x (Not y))
ruleInterchangeR _ = Left "ruleInterchangeR: Cannot construct proof"

-- | Rule of Existence
-- Suppose a term (which may contain variables as long as they are free) appears once, or multiply, in a theorem. Then any (or several, or all) of the appearances of the term may be replaced by a variable which otherwise does not occur in the theorem, and the corresponding existential quantifier must be placed in front.
ruleExistence :: Eq a => a -> [(Pos, Path, Path)] -> Proof (PropCalc (FOL a)) -> ESP (FOL a)
ruleExistence x paths (Proof y) | allSame (map (\path -> getTerm path y) paths) =
  go (Proof y) paths >>= \(Proof y) -> Right $ Proof $ PropVar (Exists x y)
  where
  go f ((pos, path1, path2):paths) = applyFOLArithRule pos path1 path2 (\_ -> Var x) f >>= \prf -> go prf paths
  go x _ = Right x
ruleExistence x [] (Proof y) | x `notElem` getBoundVars y =
  Right $ Proof $ PropVar (Exists x y)
ruleExistence _ _ _ = Left "ruleExistence: Cannot construct proof"

-- | Rule of Symmetry
-- If r=s is a theorem, then so is s=r
ruleSymmetry :: Proof (PropCalc (FOL a)) -> ESP (FOL a)
ruleSymmetry (Proof (PropVar (Eq a b))) = Right $ Proof $ PropVar (Eq b a)
ruleSymmetry _ = Left "ruleSymmetry: Cannot construct proof"

-- | Rule of Transitivity
-- If r=s and s=t are theorems, then so is r=t
ruleTransitivity :: Eq a => Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a)) -> ESP (FOL a)
ruleTransitivity (Proof (PropVar (Eq a b))) (Proof (PropVar (Eq b' c))) | b == b' = Right $ Proof $ PropVar (Eq a c)
ruleTransitivity _ _ = Left "ruleTransitivity: Cannot construct proof"

-- | Rule Add S
-- If r=t is a theorem, then Sr=St is a theorem.
ruleAddS :: Proof (PropCalc (FOL a)) -> ESP (FOL a)
ruleAddS (Proof (PropVar (Eq a b))) = Right $ Proof $ PropVar (Eq (S a) (S b))
ruleAddS _ = Left "ruleAddS: Cannot construct proof"

-- | Rule Drop S
-- If Sr=St is theorem, then r=t is a theorem.
ruleDropS :: Proof (PropCalc (FOL a)) -> ESP (FOL a)
ruleDropS (Proof (PropVar (Eq (S a) (S b)))) = Right $ Proof $ PropVar (Eq a b)
ruleDropS _ = Left "ruleDropS: Cannot construct proof"

-- | Rule of Induction
-- Let X{u} represent a well-formed formula in which the variable u is free, and X{x/u} represent the same string, with each appearance of u replaced by x. If both ∀u:<X{u}⊃X{Su/u}> and X{0/u} are theorems, then ∀u:X{u} is also a theorem.
ruleInduction :: Eq a => Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a)) -> ESP (FOL a)
ruleInduction base (Proof ih@(PropVar (ForAll x (Imp y z)))) =
  -- in base' and conc, y is Proof y because it's an assumption
  let base' = substPropCalc (Proof y) (Var x) Z
      conc  = substPropCalc (Proof y) (Var x) (S (Var x)) in
  -- similarly, z is Proof z here
  if base' == base && conc == Proof z
  then Right $ Proof $ PropVar (ForAll x y)
  else Left "ruleInduction: Cannot construct proof"
ruleInduction _ _ = Left "ruleInduction: Cannot construct proof"
