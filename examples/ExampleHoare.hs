module ExampleHoare where

import Common
import Control.Monad (join)
import ExampleCommon
import ExampleTNT
import Gentzen
import Hoare
import Imp
import PrettyPrinter
import TNT
import qualified Data.Map as M

-- Program definition
countToB =
  let l1 = CAssign A Z
      l2 = CWhile (Not (PropVar $ Eq (Var A) (Var B))) l3
      l3 = CAssign A (S (Var A))
  in CSequence l1 l2

-- Example evaluation
egEval = eval (M.fromList [(B, 3)]) countToB

pre = ruleFantasy (And (Not (PropVar $ Eq (Var A) (Var B))) (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))) $ \premise -> do
    -- ⊢ SA+C=A+SC
    eq1 <- theorem >>= ruleSpec (Var C) >>= ruleSpec (Var A) >>= ruleSymmetry
    -- ⊢ ¬¬∃C:(A+C=B)
    step1 <- ruleSepR premise >>= ruleDoubleTildeIntro
    -- ⊢ ¬¬A+SC=B
    step2 <- applyFOLRule [GoLeft] (\x -> ruleInterchangeR x >>= ruleSpec (S (Var C))) [] step1
    -- ⊢ A+SC=B
    eq2 <- ruleDoubleTildeElim step2
    -- ⊢ SA+C=B
    eq3 <- ruleTransitivity eq1 eq2
    -- ⊢ ¬A=B∧∃C:(A+C=B)→∃C:(SA+C)=B
    ruleExistence C [] eq3

-- ⊢ ∃C:(A+C=B)→∃C:(A+C=B)
post = ruleFantasy (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B)))) return

-- {∃C:(SA+C=B)} A := SA; {∃C:(A+C=B)}
step5 = hoareAssignment A (S (Var A)) (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- {¬A=B∧∃C:(A+C=B)} A := SA; {∃C:(A+C=B)}
step4 = join $ hoareConsequence <$> pre <*> step5 <*> post

-- {∃C:(0+C=B)} A := 0; {∃C:(A+C=B)}
step2 = hoareAssignment A Z (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- {∃C:(A+C=B)} (While (¬A=B) Do {A := SA;}); {¬¬A=B∧∃C:(A+C=B)}
step3 = join $ hoareWhile <$> step4

-- {∃C:(0+C=B)} A := 0; (While (¬A=B) Do {A := SA;}); {¬¬A=B∧∃C:(A+C=B)}
proof = join $ hoareSequence <$> step2 <*> step3
