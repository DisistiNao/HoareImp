module Syntax.Syntax where

import Control.Monad (join)

-- Data defs

data PropCalc a 
    = PropVar a 
    | Not (PropCalc a) 
    | And (PropCalc a) (PropCalc a) 
    | Or (PropCalc a) (PropCalc a) 
    | Imp (PropCalc a) (PropCalc a)
    deriving (Eq, Show)

newtype Proof a = Proof a

fromProof :: Proof a -> a
fromProof (Proof a) = a

type ESP a = Either String (Proof (PropCalc a))

pr :: Show a => ESP a -> String
pr (Left err) = "Error: " ++ err
pr (Right (Proof x)) = "OK: " ++ show x

data Pos = GoLeft | GoRight
type Path = [Pos]

-- Helper functions

applyPropRule :: Path -> (Proof (PropCalc a) -> ESP a) -> Proof (PropCalc a) -> ESP a
applyPropRule xs f (Proof x) = go xs f x
    where
        go :: Path -> (Proof (PropCalc a) -> ESP a) -> PropCalc a -> ESP a
        go (_:xs) f (Not x) = go xs f x >>= \(Proof x) -> Right $ Proof $ Not x
        go (GoLeft:xs) f (And x y) = go xs f x >>= \(Proof x) -> Right $ Proof $ And x y
        go (GoLeft:xs) f (Or x y) = go xs f x >>= \(Proof x) -> Right $ Proof $ Or x y
        go (GoLeft:xs) f (Imp x y) = go xs f x >>= \(Proof x) -> Right $ Proof $ Imp x y
        go (GoRight:xs) f (And x y) = go xs f x >>= \(Proof x) -> Right $ Proof $ And x y
        go (GoRight:xs) f (Or x y) = go xs f x >>= \(Proof x) -> Right $ Proof $ Or x y
        go (GoRight:xs) f (Imp x y) = go xs f x >>= \(Proof x) -> Right $ Proof $ Imp x y
        go _ f x = f (Proof x)

-- Rules

-- Joining Rule (And-introduction)
-- If x and y are theorems, then $< x \land y >$ is a theorem.
ruleJoin :: Proof (PropCalc a) -> Proof (PropCalc a) -> ESP a
ruleJoin (Proof x) (Proof y) = Right $ Proof $ And x y

-- Sep Rule (And-elimination)
-- If $< x \land y >$ is a theorem, then both x and y are theorems.
ruleSepL :: Proof (PropCalc a) -> ESP a
ruleSepL (Proof (And x _)) = Right $ Proof x
ruleSepL _ = Left "ruleSepL: Cannot construct proof"

ruleSepR :: Proof (PropCalc a) -> ESP a
ruleSepR (Proof (And _ y)) = Right $ Proof y
ruleSepR _ = Left "ruleSepR: Cannot construct proof"

-- Fantasy Rule (Implication-introduction)
-- If x were a theorem, y would be a theorem $ (< x \rightarrow y >) $.
ruleFantasy :: PropCalc a -> (Proof (PropCalc a) -> ESP a) -> ESP a
ruleFantasy x f = f (Proof x) >>= \(Proof y) -> Right $ Proof $ Imp x y

-- Rule of Detachment (Implication-elimination)
-- If x and $ < x \rightarrow y > $ are both theorems, then y is a theorem.
ruleDetachment :: Eq a => Proof (PropCalc a) -> Proof (PropCalc a) -> ESP a
ruleDetachment (Proof x) (Proof (Imp x' y)) | x == x' = Right $ Proof y
ruleDetachment _ _ = Left "ruleDetachment: Cannot construct proof"

-- Double-Tilde Rule (Double negation)
-- The string $\lnot\lnot$ can be deleted from any theorem. It can also be inserted into any 
-- theorem, provided that the resulting string is itself well-formed.
ruleDoubleTildeIntro :: Proof (PropCalc a) -> ESP a
ruleDoubleTildeIntro (Proof x) = Right $ Proof $ Not (Not x)

ruleDoubleTildeElim :: Proof (PropCalc a) -> ESP a
ruleDoubleTildeElim (Proof (Not (Not x))) = Right $ Proof x
ruleDoubleTildeElim _ = Left "ruleDoubleTildeElim: Cannot construct proof"

-- Contrapositive Rule
-- $ < x \rightarrow y > $ and $ < \lnot y \rightarrow \lnot x > $ are interchangeable.
ruleContrapositive :: Proof (PropCalc a) -> ESP a
ruleContrapositive (Proof (Imp (Not y) (Not x))) = Right $ Proof $ Imp x y
ruleContrapositive (Proof (Imp x y)) = Right $ Proof $ Imp (Not y) (Not x)
ruleContrapositive _ = Left "ruleContrapositive: Cannot construct proof"

-- Switcheroo Rule
-- $ < x \lor y > $ and $ < \lnot x \rightarrow y > $ are interchangeable.
ruleSwitcheroo :: Proof (PropCalc a) -> ESP a
ruleSwitcheroo (Proof (Or x y)) = Right $ Proof $ Imp (Not x) y
ruleSwitcheroo (Proof (Imp (Not x) y)) = Right $ Proof $ Or x y
ruleSwitcheroo _ = Left "ruleSwitcheroo: Cannot construct proof"

-- De Morgan’s Rule
-- $ < \lnot x ∧ \lnot y > $ and $ \lnot < x \lor y > $ are interchangeable.
ruleDeMorgan :: Proof (PropCalc a) -> ESP a
ruleDeMorgan (Proof (And (Not x) (Not y))) = Right $ Proof $ Not (Or x y)
ruleDeMorgan (Proof (Not (Or x y))) = Right $ Proof $ And (Not x) (Not y)
ruleDeMorgan _ = Left "ruleDeMorgan: Cannot construct proof"

{-
Test 1
    putStrLn $ pr $ ruleFantasy (And (PropVar "A") (PropVar "B")) (\pq -> join $ ruleJoin <$> ruleSepR pq <*> ruleSepL pq)
    
    Result: $ A \land B \rightarrow B \land A $
-}

{-
Test 2
    putStrLn $ pr $ ruleFantasy (Or (PropVar "A") (PropVar "B")) (applyPropRule [GoRight] ruleDoubleTildeIntro)
    
    Result: $ A \lor B \rightarrow A \lor \lnot \lnot B $
-}

{- 
Test 3
    putStrLn $ pr $ ruleFantasy (And (PropVar "A") (PropVar "B")) return >>= applyPropRule [GoLeft] ruleSepL
    
    Result: $ A \rightarrow A \land B $
-}

{-
Test 4
    :{
    putStrLn $ pr $ ruleFantasy (Or (PropVar "A") (PropVar "B")) $ \premise -> do
    step1 <- ruleSwitcheroo premise
    step2 <- ruleContrapositive step1
    step3 <- (ruleFantasy (Not (PropVar "B")) $ \premise2 -> do
    step4 <- ruleDetachment premise2 step2
    ruleDoubleTildeElim step4)
    prfBorA <- ruleSwitcheroo step3
    step5 <- ruleSwitcheroo prfBorA
    step6 <- ruleContrapositive step5
    ruleSwitcheroo step6
    :}
    
    Result: $ A \lor B \rightarrow A \lor \lnot \lnot B $
-}