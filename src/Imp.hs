module Imp where

import Common
import Gentzen
import PrettyPrinter
import TNT
import qualified Data.Map as M

data Command a =
  CSkip
  | CAssign a (Arith a)
  | CSequence (Command a) (Command a)
  | CIfElse (PropCalc (FOL a)) (Command a) (Command a)
  | CWhile (PropCalc (FOL a)) (Command a)
  | CAssert (PropCalc (FOL a)) (Command a) (PropCalc (FOL a))
  deriving (Show)

instance Pretty a => Pretty (Command a) where
  prPrec q CSkip           = ";"
  prPrec q (CAssign x y)   = prPrec q x ++ " := " ++ prPrec q y ++ ";"
  prPrec q (CSequence x y) = prPrec q x ++ " " ++ prPrec q y
  prPrec q (CIfElse x y z) = "if (" ++ prPrec q x ++ ") then {" ++ prPrec q y ++ "} else {" ++ prPrec q z ++ "};"
  prPrec q (CWhile x y)    = "while (" ++ prPrec q x ++ ") do {" ++ prPrec q y ++ "};"
  prPrec q (CAssert x y z) = "assert {" ++ prPrec q x ++ "} (" ++ prPrec q y ++ ") {" ++ prPrec q z ++ "};"

type Context a = M.Map a Integer

aeval :: (Ord a, Eq a) => Context a -> Arith a -> Either String Integer
aeval ctx (Var v)        = if M.member v ctx then Right (ctx M.! v) else Left "Element not found"
aeval ctx Z              = Right 0
aeval ctx (S a)          = aeval ctx a >>= \a -> Right $ 1 + a
aeval ctx (Plus a1 a2)   = aeval ctx a1 >>= \a1 -> aeval ctx a2 >>= \a2 -> Right $ a1 + a2
aeval ctx (Mult a1 a2)   = aeval ctx a1 >>= \a1 -> aeval ctx a2 >>= \a2 -> Right $ a1 * a2

beval :: (Ord a, Eq a) => Context a -> PropCalc (FOL a) -> Either String Bool
beval ctx (PropVar (Eq a1 a2))   = aeval ctx a1 >>= \a1 -> aeval ctx a2 >>= \a2 -> Right $ a1 == a2
beval ctx (PropVar (ForAll x b)) = beval ctx b
beval ctx (PropVar (Exists x b)) = beval ctx b
beval ctx (Not b)     = beval ctx b >>= \b -> Right $ not b
beval ctx (And b1 b2) = beval ctx b1 >>= \b1 -> beval ctx b2 >>= \b2 -> Right $ b1 && b2
beval ctx (Or b1 b2)  = beval ctx b1 >>= \b1 -> beval ctx b2 >>= \b2 -> Right $ b1 || b2
beval ctx (Imp b1 b2) = beval ctx b1 >>= \b1 -> beval ctx b2 >>= \b2 -> Right $ not b1 || b2

eval :: (Ord a, Eq a) => Context a -> Command a -> Either String (Context a)
eval ctx CSkip             = Right ctx
eval ctx (CAssign c v)     = aeval ctx v >>= \v -> Right $ M.insert c v ctx
eval ctx (CSequence c1 c2) = let ctx' = eval ctx c1 in ctx' >>= (\ctx'' -> eval ctx'' c2)
eval ctx (CIfElse b c1 c2) = beval ctx b >>= \b -> eval ctx $ if b then c1 else c2
eval ctx (CWhile b c)      = beval ctx b >>= \b' ->
  if b'
  then let ctx' = eval ctx c in ctx' >>= (\ctx'' -> eval ctx'' (CWhile b c))
  else Right ctx
eval ctx (CAssert b1 c b2) = beval ctx b1 >>= \b1 ->
  if b1
  then eval ctx c >>=
       (\ctx' -> beval ctx' b2 >>= \b2 ->
                  if b2
                  then Right ctx'
                  else Left "Assert: Post-condition does not match!")
  else Left "Assert: Pre-condition does not match!"

assert :: (Ord a, Eq a) => Context a -> PropCalc (FOL a) -> Command a -> PropCalc (FOL a) -> Either String Bool
assert ctx boolPre cmd boolPost = let res = eval ctx cmd in go res
  where
  go (Right ctx') = beval ctx boolPre >>= \boolPre -> beval ctx' boolPost >>= \boolPost -> Right $ boolPre && boolPost
  go _            = Right False
