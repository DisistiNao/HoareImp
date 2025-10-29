module CostExp where

import Common
import Costs
import Gentzen
import Hoare
import Imp
import PrettyPrinter
import TNT

data CostHoareTriple a =
    CostHoareTriple (HoareTriple a) Cost
    deriving (Show)

type ESCost a = Either String (CostHoareTriple a)

instance Pretty a => Pretty (CostHoareTriple a) where
    prPrec q (CostHoareTriple (HoareTriple pre c post) cost) =
        "{" ++ prPrec q pre ++ "} "
        ++ prPrec q c
        ++ " {" ++ prPrec q post ++ " | " ++ prettyCost cost ++ "}"

costSkip :: PropCalc (FOL a) -> ESCost a
costSkip q = Right $ CostHoareTriple (HoareTriple q CSkip q) (CConst 0)

costAssignment :: Eq a => a -> Arith a -> PropCalc (FOL a) -> ESCost a
costAssignment v e q =
    Right $ CostHoareTriple
        (HoareTriple
            (fromProof (substPropCalc (Proof q) (Var v) e))
            (CAssign v e)
            q)
        (costAExpr e + CConst 1)

costConsequence :: Eq a => Proof (PropCalc (FOL a)) -> CostHoareTriple a -> Proof (PropCalc (FOL a)) -> ESCost a
costConsequence (Proof (Imp p1 p2)) (CostHoareTriple (HoareTriple p2' c q2) costValue) (Proof (Imp q2' q1))
  | p2 == p2' && q2 == q2' = Right $ CostHoareTriple (HoareTriple p1 c q1) (costValue + CConst 0)
costConsequence _ _ _ = Left "costConsequence: Cannot construct proof"

costSequence :: Eq a => CostHoareTriple a -> CostHoareTriple a -> ESCost a
costSequence (CostHoareTriple (HoareTriple p c1 q1) cost1)
             (CostHoareTriple (HoareTriple q2 c2 r) cost2)
  | q1 == q2 = Right $ CostHoareTriple (HoareTriple p (CSequence c1 c2) r) (cost1 + cost2)
costSequence _ _ = Left "costSequence: Cannot construct proof"

costConditional :: Eq a => CostHoareTriple a -> CostHoareTriple a -> ESCost a
costConditional (CostHoareTriple (HoareTriple (And b1 p1) c1 q1) cost1)
                (CostHoareTriple (HoareTriple (And (Not b2) p2) c2 q2) cost2)
  | b1 == b2 && p1 == p2 && q1 == q2 =
      Right $ CostHoareTriple (HoareTriple p1 (CIfElse b1 c1 c2) q1) (costBExpr b1 + (max cost1 cost2))
costConditional _ _ = Left "costConditional: Cannot construct proof"