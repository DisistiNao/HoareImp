module Costs where

import Gentzen
import TNT

data Cost
  = CConst Int
  | CVar String Int
  | CAdd Cost Cost
  deriving (Eq, Show, Ord)

instance Num Cost where
  (+) (CConst a) (CConst b) = CConst (a + b)
  (+) (CConst a) e = simplify (CAdd (CConst a) e)
  (+) e (CConst a) = simplify (CAdd e (CConst a))
  (+) e1 e2 = simplify (CAdd e1 e2)

  (*) (CConst a) (CConst b) = CConst (a * b)
  (*) (CConst a) (CVar v c) = CVar v (a * c)
  (*) (CVar v c) (CConst a) = CVar v (a * c)
  (*) _ _ = error "Multiplicação entre custos não suportada"

  abs = id
  signum _ = 1
  fromInteger n = CConst (fromInteger n)
  negate (CConst n) = CConst (negate n)
  negate (CVar v c) = CVar v (negate c)
  negate (CAdd e1 e2) = CAdd (negate e1) (negate e2)

simplify :: Cost -> Cost
simplify (CAdd (CConst a) (CConst b)) = CConst (a + b)
simplify (CAdd (CConst 0) e) = simplify e
simplify (CAdd e (CConst 0)) = simplify e
simplify e = e

prettyCost :: Cost -> String
prettyCost (CConst n) = show n
prettyCost (CVar v 1) = v
prettyCost (CVar v c) = show c ++ v
prettyCost (CAdd e1 e2) = prettyCost e1 ++ " + " ++ prettyCost e2

costAExpr :: Arith a -> Cost
costAExpr (Var _) = CConst 1
costAExpr Z = CConst 0
costAExpr (S a) = costAExpr a + CConst 0
costAExpr (Plus a1 a2) = costAExpr a1 + costAExpr a2 + CConst 1
costAExpr (Mult a1 a2) = costAExpr a1 + costAExpr a2 + CConst 1

costBExpr :: PropCalc a -> Cost
costBExpr (PropVar _) = CConst 1
costBExpr (Not a) = costBExpr a + CConst 1
costBExpr (And a1 a2) = costBExpr a1 + costBExpr a2 + CConst 1
costBExpr (Or a1 a2) = costBExpr a1 + costBExpr a2 + CConst 1
costBExpr (Imp a1 a2) = costBExpr a1 + costBExpr a2 + CConst 1