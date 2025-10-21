module ExampleHoare2 where

import Control.Monad (join)
import ExampleCommon
import Gentzen
import Hoare
import Imp
import PrettyPrinter
import TNT
import qualified Data.Map as M

-- Program definition
swapAB =
  let l1 = CAssign C (Var A)
      l2 = CAssign A (Var B)
      l3 = CAssign B (Var C)
      in CSequence l1 (CSequence l2 l3)

-- Example evaluation
egEval = eval (M.fromList [(A, 3), (B, 5)]) swapAB

-- {A=D∧B=E} C := A; {C=D∧B=E}
ht1 = hoareAssignment C (Var A) (And (PropVar $ Eq (Var C) (Var D)) (PropVar $ Eq (Var B) (Var E)))
-- {C=D∧B=E} A := B; {C=D∧A=E}
ht2 = hoareAssignment A (Var B) (And (PropVar $ Eq (Var C) (Var D)) (PropVar $ Eq (Var A) (Var E)))
-- {C=D∧A=E} B := C; {B=D∧A=E}
ht3 = hoareAssignment B (Var C) (And (PropVar $ Eq (Var B) (Var D)) (PropVar $ Eq (Var A) (Var E)))

-- {A=D∧B=E} C := A; A := B; B := C; {B=D∧A=E}
proof = join $ hoareSequence <$> ht1 <*> join (hoareSequence <$> ht2 <*> ht3)
