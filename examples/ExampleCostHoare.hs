module ExampleCostHoare where

import Common
import Costs
import CostExp
import Gentzen
import Hoare
import Imp
import PrettyPrinter
import TNT
import ExampleCommon
import ExampleTNT
import Control.Monad (join)

-- =========================================================
-- Example: Skip
-- =========================================================

exampleSkip :: IO ()
exampleSkip =
  putStrLn $ pr $ costSkip (PropVar (Eq (Var A) (S (S (S Z)))))

-- =========================================================
-- Example: Assignment
-- =========================================================

exampleAssignment :: IO ()
exampleAssignment =
  putStrLn $ pr $ costAssignment A (Plus (Var B) (S Z))
    (And (PropVar (Eq (Var A) (S (S Z)))) (PropVar (Eq Z Z)))

-- =========================================================
-- Example: Consequence 1
-- =========================================================

exampleConsequence1 :: IO ()
exampleConsequence1 = do
  let ht = costAssignment A (Plus (Var B) (S Z))
            (And (PropVar (Eq (Var A) (S (S Z)))) (PropVar (Eq Z Z)))
  let pre = ruleFantasy (And (PropVar (Eq (Plus (Var B) (S Z)) (S (S Z)))) (PropVar (Eq Z Z))) return
  let post = ruleFantasy (And (PropVar (Eq (Var A) (S (S Z)))) (PropVar (Eq Z Z))) ruleSepL
  putStrLn $ pr $ join $ costConsequence <$> pre <*> ht <*> post

-- =========================================================
-- Example: Consequence 2
-- =========================================================

exampleConsequence2 :: IO ()
exampleConsequence2 = do
  let ht = costAssignment A (Plus (Var B) (S Z)) (PropVar (Eq (Var A) (S (S Z))))
  let pre = ruleFantasy (And (PropVar (Eq (Plus (Var B) (S Z)) (S (S Z)))) (PropVar (Eq Z Z))) ruleSepL
  let post = ruleFantasy (PropVar (Eq (Var A) (S (S Z)))) return
  putStrLn $ pr $ join $ costConsequence <$> pre <*> ht <*> post

-- =========================================================
-- Example: Sequence
-- =========================================================

exampleSequence :: IO ()
exampleSequence = do
  let c1 = costAssignment B Z (And (PropVar $ Eq (Var B) Z) (PropVar $ Eq (Var A) (Var A)))
  let c2 = costAssignment C (Var A) (And (PropVar $ Eq (Var B) Z) (PropVar $ Eq (Var C) (Var A)))
  putStrLn $ pr $ join $ costSequence <$> c1 <*> c2

-- =========================================================
-- Example: Conditional
-- =========================================================

exampleConditional :: IO ()
exampleConditional = do
  let ht1 = costSkip (And (Not $ PropVar (Eq (Var A) Z)) (PropVar $ Eq Z Z))
  let ht2 = costAssignment A (S (Var A)) (And (Not $ PropVar (Eq (Var A) Z)) (PropVar $ Eq Z Z))

  let prf1 =
        ruleFantasy (And (PropVar (Eq (Var A) Z)) (PropVar $ Eq Z Z)) $ \pq ->
          join $ ruleJoin
            <$> (axiom1 (Var A) >>= ruleSpec (Var A))
            <*> ruleSepR pq

  let prf2 = ruleFantasy (And (Not $ PropVar (Eq (Var A) Z)) (PropVar $ Eq Z Z)) return

  let ht3 = join $ costConsequence <$> prf1 <*> ht2 <*> prf2

  putStrLn $ pr $ join $ costConditional <$> ht3 <*> ht1

-- =========================================================
-- Run all examples
-- =========================================================

main :: IO ()
main = do
  putStrLn "=== Skip ==="
  exampleSkip
  putStrLn "\n=== Assignment ==="
  exampleAssignment
  putStrLn "\n=== Consequence 1 ==="
  exampleConsequence1
  putStrLn "\n=== Consequence 2 ==="
  exampleConsequence2
  putStrLn "\n=== Sequence ==="
  exampleSequence
  putStrLn "\n=== Conditional ==="
  exampleConditional
