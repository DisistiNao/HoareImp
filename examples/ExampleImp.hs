module ExampleImp where

import ExampleCommon
import Gentzen
import Imp
import PrettyPrinter
import TNT
import qualified Data.Map as M

-- Program definition
-- A = B!
factB =
  let l1 = CAssign C Z
      l2 = CAssign A (S Z)
      l3 = CWhile (Not (PropVar $ Eq (Var C) (Var B))) (CSequence l4 l5)
      l4 = CAssign C (S (Var C))
      l5 = CAssign A (Mult (Var A) (Var C))
  in CSequence l1 (CSequence l2 l3)
--  in CSequence (CSequence l1 l2) l3 -- Since ; is associative, we can also use this

{-
c = 0;
a = 1;
while (c != b) {
  c += 1;
  a *= c;
}
-}

-- Example evaluation
egEval = eval (M.fromList [(B, 7)]) factB
