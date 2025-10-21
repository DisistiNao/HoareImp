module ExampleTNT2 where

import Common
import Control.Monad (join)
import ExampleCommon
import Gentzen
import PrettyPrinter
import TNT

main = do
  putStrLn "Specific example"
  putStrLn $ pr thm
  putStrLn "Addition"
  mapM_ (\(n,p) -> putStrLn $ show n ++ ": " ++ pr p) $ zip [1..] [prop1,prop2,prop3,prop4,prop5]
  putStrLn "Multiplication"
  mapM_ (\(n,p) -> putStrLn $ show n ++ ": " ++ pr p) $ zip [6..] [prop6,prop7,prop8]
  putStrLn "Example strictness of `applyFOLRule`"
  putStrLn $ pr $ let formula = Proof $ And (PropVar $ Eq (Var A) (Var B)) (PropVar $ Exists B (PropVar (Eq (Var B) (Var C)))) in applyFOLRule [GoLeft] (\prfAeqB -> applyFOLRule [GoRight,GoLeft] (ruleTransitivity prfAeqB) [] formula) [] formula
  putStrLn $ pr $ let formula = Proof $ And (PropVar $ Eq (Var A) (Var B)) (PropVar $ Exists B (PropVar (Eq (Var B) (Var C)))) in applyFOLRule [GoLeft] (\prfAeqB -> applyFOLRule [GoRight,GoLeft] (ruleTransitivity prfAeqB) [prfAeqB] formula) [] formula

-- ⊢ S0+S0=SS0
thm = do
  eq1 <- axiom3 (Var A) (Var B) >>= ruleSpec (S Z) >>= ruleSpec Z
  eq2 <- axiom2 (Var A) >>= ruleSpec (S Z) >>= ruleAddS
  ruleTransitivity eq1 eq2

{- Prop1 -}
-- ⊢ 0=0+0
prop1base = do
  step <- axiom2 (Var A) >>= ruleSpec Z
  ruleSymmetry step

-- ⊢ ∀A:<A=0+A→SA=0+SA>
prop1hyp = do
  imp <- ruleFantasy (PropVar (Eq (Var A) (Plus Z (Var A)))) $ \premise -> do
    -- ⊢ A=0+A→SA=S(0+A)
    eq1 <- ruleAddS premise
    step <- axiom3 (Var A) (Var B) >>= ruleSpec Z >>= ruleSpec (Var A)
    -- ⊢ S(0+A)=0+SA
    eq2 <- ruleSymmetry step
    ruleTransitivity eq1 eq2
  ruleGeneralize A [] imp

-- ⊢ ∀A:(A=0+A)
prop1 = join $ ruleInduction <$> prop1base <*> prop1hyp

{- Prop2 -}
-- ⊢ SA+0=S(A+0)
prop2base = do
  -- ⊢ SA+0=SA
  eq1 <- axiom2 (Var A) >>= ruleSpec (S (Var A))
  -- ⊢ A+0=A
  eq2 <- axiom2 (Var A) >>= ruleSpec (Var A)
  -- ⊢ S(A+0)=SA
  eq2 <- ruleAddS eq2
  -- ⊢ SA=S(A+0)
  eq2 <- ruleSymmetry eq2
  ruleTransitivity eq1 eq2

-- ⊢ ∀A:<SA+B=S(A+B)→SA+SB=S(A+SB)>
prop2hyp = do
  imp <- ruleFantasy (PropVar (Eq (Plus (S (Var A)) (Var B)) (S (Plus (Var A) (Var B))))) $ \premise -> do
    -- ⊢ SA+SB=S(SA+B)
    eq1 <- axiom3 (Var A) (Var B) >>= ruleSpec (S (Var A)) >>= ruleSpec (Var B)
    -- ⊢ S(SA+B)=SS(A+B)
    eq2 <- ruleAddS premise
    -- ⊢ SA+SB=SS(A+B)
    eq3 <- ruleTransitivity eq1 eq2
    -- ⊢ A+SB=S(A+B)
    eq4 <- axiom3 (Var A) (Var B) >>= ruleSpec (Var A) >>= ruleSpec (Var B)
    -- ⊢ S(A+SB)=SS(A+B)
    eq4' <- ruleAddS eq4
    -- ⊢ SS(A+B)=S(A+SB)
    eq4'' <- ruleSymmetry eq4'
    ruleTransitivity eq3 eq4''
  ruleGeneralize B [] imp

-- ⊢ ∀A:∀B:(SA+B=S(A+B))
prop2 = join (ruleInduction <$> prop2base <*> prop2hyp) >>= ruleGeneralize A []

{- Prop3 -}
-- ⊢ B=C→0+B=0+C
prop3base = ruleFantasy (PropVar (Eq (Var B) (Var C))) $ \premise -> do
  step1 <- prop1 >>= ruleSpec (Var B)
  -- ⊢ 0+B=B
  eq1 <- ruleSymmetry step1
  -- ⊢ C=0+C
  eq2 <- prop1 >>= ruleSpec (Var C)
  -- ⊢ 0+B=C
  eq3 <- ruleTransitivity eq1 premise
  ruleTransitivity eq3 eq2

-- ⊢ ∀A:<<B=C→A+B=A+C>→B=C→SA+B=SA+C>
prop3hyp = do
  imp <- ruleFantasy (Imp (PropVar (Eq (Var B) (Var C))) (PropVar (Eq (Plus (Var A) (Var B)) (Plus (Var A) (Var C))))) $ \premise -> do
   ruleFantasy (PropVar (Eq (Var B) (Var C))) $ \premise2 -> do
     -- ⊢ A+B=A+C
     eq1 <- ruleDetachment premise2 premise
     -- ⊢ S(A+B)=S(A+C)
     eq2 <- ruleAddS eq1
     -- ⊢ SA+B=S(A+B)
     eq3 <- prop2 >>= ruleSpec (Var A) >>= ruleSpec (Var B)
     eq3' <- prop2 >>= ruleSpec (Var A) >>= ruleSpec (Var C)
     -- ⊢ S(A+C)=SA+C
     eq4 <- ruleSymmetry eq3'
     -- ⊢ SA+B=S(A+C)
     eq5 <- ruleTransitivity eq3 eq2
     ruleTransitivity eq5 eq4
  ruleGeneralize A [] imp

-- ⊢ ∀A:∀B:∀C:<B=C→A+B=A+C>
prop3 = join (ruleInduction <$> prop3base <*> prop3hyp) >>= ruleSpec (Var A) >>= ruleGeneralize C [] >>= ruleGeneralize B [] >>= ruleGeneralize A []

{- Prop4 -}
-- ⊢ A+0=0+A
prop4base = do
  eq1 <- axiom2 (Var A) >>= ruleSpec (Var A)
  eq2 <- prop1 >>= ruleSpec (Var A)
  ruleTransitivity eq1 eq2

-- ⊢ ∀B:<A+B=B+A→A+SB=SB+A>
prop4hyp = do
  imp <- ruleFantasy (PropVar (Eq (Plus (Var A) (Var B)) (Plus (Var B) (Var A)))) $ \premise -> do
    -- ⊢ A+SB=S(A+B)
    eq1 <- axiom3 (Var A) (Var B) >>= ruleSpec (Var A) >>= ruleSpec (Var B)
    -- ⊢ S(A+B)=S(B+A)
    eq2 <- ruleAddS premise
    -- ⊢ A+SB=S(B+A)
    eq3 <- ruleTransitivity eq1 eq2
    -- ⊢ SB+A=S(B+A)
    eq4 <- prop2 >>= ruleSpec (Var C) >>= ruleSpec (Var A) >>= ruleGeneralize C [premise] >>= ruleSpec (Var B)
    -- ⊢ S(B+A)=SB+A
    eq4' <- ruleSymmetry eq4
    ruleTransitivity eq3 eq4'
  ruleGeneralize B [] imp

-- ⊢ ∀A:∀B:(A+B=B+A)
prop4 = join (ruleInduction <$> prop4base <*> prop4hyp) >>= ruleGeneralize A []

{- Prop5 -}
-- ⊢ A+B+0=(A+B)+0
prop5base = do
  -- ⊢ B+0=B
  eq1 <- axiom2 (Var A) >>= ruleSpec (Var B)
  -- ⊢ B+0=B→A+B+0=A+B
  eq2 <- prop3 >>= ruleSpec (Var A) >>= ruleSpec (Plus (Var B) Z) >>= ruleSpec (Var B)
  -- ⊢ A+B+0=A+B
  eq3 <- ruleDetachment eq1 eq2
  -- ⊢ A+B=(A+B)+0
  eq4 <- axiom2 (Var A) >>= ruleSpec (Plus (Var A) (Var B))
  eq4 <- ruleSymmetry eq4
  -- ⊢ A+B+0=(A+B)+0
  eq5 <- ruleTransitivity eq3 eq4
  ruleTransitivity eq3 eq4

-- ⊢ ∀C:<A+B+C=(A+B)+C→A+B+SC=(A+B)+SC>
prop5hyp = do
  imp <- ruleFantasy (PropVar (Eq (Plus (Var A) (Plus (Var B) (Var C))) (Plus (Plus (Var A) (Var B)) (Var C)))) $ \premise -> do
    -- ⊢ B+SC=S(B+C)
    eq1 <- axiom3 (Var A) (Var B) >>= applyFOLRule [GoRight] (ruleSpec (Var C)) [] >>= ruleSpec (Var B)
    -- ⊢ B+SC=S(B+C)→A+B+SC=A+S(B+C)
    eq2 <- prop3 >>= ruleSpec (Var A) >>= ruleSpec (Var E) >>= ruleSpec (S (Plus (Var D) (Var C))) >>= ruleGeneralize E [premise] >>= ruleSpec (Plus (Var B) (S (Var C))) >>= ruleGeneralize D [premise] >>= ruleSpec (Var B)
    -- ⊢ A+B+SC=A+S(B+C)
    eq3 <- ruleDetachment eq1 eq2
    -- ⊢ A+S(B+C)=S(A+B+C)
    eq4 <- axiom3 (Var A) (Var B) >>= ruleSpec (Var A) >>= ruleSpec (Plus (Var B) (Var C))
    -- ⊢ A+B+SC=S(A+B+C)
    eq5 <- ruleTransitivity eq3 eq4
    -- ⊢ S(A+B+C)=S((A+B)+C)
    eq6 <- ruleAddS premise
    -- ⊢ A+B+SC=S((A+B)+C)
    eq7 <- ruleTransitivity eq5 eq6
    -- ⊢ S((A+B)+C)=(A+B)+SC
    eq8 <- axiom3 (Var A) (Var B) >>= applyFOLRule [GoRight] (ruleSpec (Var C)) [] >>= ruleSpec (Plus (Var A) (Var B))
    eq9 <- ruleSymmetry eq8
    ruleTransitivity eq7 eq9
  ruleGeneralize C [] imp

-- ⊢ ∀A:∀B:∀C:(A+B+C=(A+B)+C)
prop5 = join (ruleInduction <$> prop5base <*> prop5hyp) >>= ruleGeneralize B [] >>= ruleGeneralize A []

{- Prop6 -}
-- ⊢ 0*0=0
prop6base = axiom4 (Var A) >>= ruleSpec Z

-- ⊢ ∀A:<0*A=0→0*SA=0>
prop6hyp = do
  imp <- ruleFantasy (PropVar (Eq (Mult Z (Var A)) Z)) $ \premise -> do
    -- ⊢ 0*SA=0*A+0
    eq1 <- axiom5 (Var A) (Var B) >>= ruleSpec Z >>= ruleSpec (Var A)
    -- ⊢ 0*A+0=0*A
    eq2 <- axiom2 (Var A) >>= ruleSpec (Mult Z (Var A))
    -- ⊢ 0*SA=0*A
    eq3 <- ruleTransitivity eq1 eq2
    ruleTransitivity eq3 premise
  ruleGeneralize A [] imp

-- ⊢ ∀A:(0*A=0)
prop6 = join (ruleInduction <$> prop6base <*> prop6hyp)

{- Prop7 -}
-- ⊢ SA*0=A*0+0
prop7base = do
  -- ⊢ SA*0=0
  eq1 <- axiom4 (Var A) >>= ruleSpec (S (Var A))
  -- ⊢ 0=0+0
  eq2 <- axiom2 (Var A) >>= ruleSpec Z
  eq2 <- ruleSymmetry eq2
  -- ⊢ SA*0=0+0
  eq2' <- ruleTransitivity eq1 eq2
  -- ⊢ A*0=0
  eq3 <- axiom4 (Var A) >>= ruleSpec (Var A)
  eq4 <- prop3 >>= ruleSpec Z >>= ruleSpec (Mult (Var A) Z) >>= ruleSpec Z
  -- ⊢ 0+0=0+A*0
  eq4' <- ruleDetachment eq3 eq4
  eq4' <- ruleSymmetry eq4'
  -- ⊢ SA*0=0+0
  eq5 <- ruleTransitivity eq1 eq2
  -- ⊢ SA*0=0+A*0
  eq6 <- ruleTransitivity eq5 eq4'
  -- ⊢ 0+A*0=A*0+0
  eq7 <- prop4 >>= ruleSpec Z >>= ruleSpec (Mult (Var A) Z)
  ruleTransitivity eq6 eq7

-- ⊢ ∀B:<SA*B=A*B+B→SA*SB=A*SB+SB>
prop7hyp = do
  imp <- ruleFantasy (PropVar (Eq (Mult (S (Var A)) (Var B)) (Plus (Mult (Var A) (Var B)) (Var B)))) $ \premise -> do
    -- ⊢ SA*SB=SA*B+SA
    eq1 <- axiom5 (Var A) (Var B) >>= ruleSpec (S (Var A)) >>= ruleSpec (Var B)
    -- ⊢ SA*B+SA=SA+SA*B
    eq2 <- prop4 >>= ruleSpec (Var D) >>= ruleSpec (S (Var A)) >>= ruleGeneralize D [premise] >>= ruleSpec (Mult (S (Var A)) (Var B))
    eq2' <- ruleTransitivity eq1 eq2
    eq3 <- prop3 >>= ruleSpec (S (Var A)) >>= ruleSpec (Mult (S (Var A)) (Var B)) >>= ruleSpec (Plus (Mult (Var A) (Var B)) (Var B))
    eq3' <- ruleDetachment premise eq3
    -- ⊢ SA*SB=SA+A*B+B
    eq4 <- ruleTransitivity eq2' eq3'
    -- ⊢ SA+A*B+B=(A*B+B)+SA
    eq5 <- prop4 >>= ruleSpec (Var D) >>= ruleSpec (Plus (Mult (Var A) (Var B)) (Var B)) >>= ruleGeneralize D [premise]
    eq5 <- ruleSpec (S (Var A)) eq5
    -- ⊢ SA*SB=(A*B+B)+SA
    eq6 <- ruleTransitivity eq4 eq5
    -- ⊢ A*B+B+SA=(A*B+B)+SA
    eq7 <- prop5 >>= applyFOLRule [GoRight] (ruleSpec (Var B)) [] >>= ruleSpec (Mult (Var A) (Var B))>>= ruleSpec (S (Var A))
    eq7 <- ruleSymmetry eq7
    -- ⊢ SA*SB=A*B+B+SA
    eq8 <- ruleTransitivity eq6 eq7
    -- ⊢ B+SA=S(B+A)
    eq9 <- axiom3 (Var A) (Var B) >>= ruleSpec (Var D) >>= ruleSpec (Var A) >>= ruleGeneralize D [premise] >>= ruleSpec (Var B)
    -- ⊢ B+SA=S(B+A)→SA+B+SA=SA+S(B+A)
    eq9' <- prop3 >>= ruleSpec (Var D) >>= ruleSpec (Plus (Var B) (S (Var A))) >>= ruleSpec (S (Plus (Var B) (Var A))) >>= ruleGeneralize D [premise] >>= ruleSpec (Mult (Var A) (Var B))
    -- ⊢ A*B+B+SA=A*B+S(B+A)
    eq9'' <- ruleDetachment eq9 eq9'
    -- ⊢ SA*SB=A*B+S(B+A)
    eq10 <- ruleTransitivity eq8 eq9''
    -- ⊢ S(B+A)=S(A+B)
    eq11 <- prop4 >>= ruleSpec (Var D) >>= ruleSpec (Var A) >>= ruleGeneralize D [premise]  >>= ruleSpec (Var B)
    eq11 <- ruleAddS eq11
    -- ⊢ S(B+A)=S(A+B)→A*B+S(B+A)=A*B+S(A+B)
    eq11' <- prop3 >>= ruleSpec (Var D) >>= ruleSpec (S (Plus (Var B) (Var A))) >>= ruleSpec (S (Plus (Var A) (Var B))) >>= ruleGeneralize D [premise] >>= ruleSpec (Mult (Var A) (Var B))
    -- ⊢ A*B+S(B+A)=A*B+S(A+B)
    eq11'' <- ruleDetachment eq11 eq11'
    -- ⊢ SA*SB=A*B+S(A+B)
    eq12 <- ruleTransitivity eq10 eq11''
    -- ⊢ A+SB=S(A+B)
    eq13 <- axiom3 (Var A) (Var B) >>= ruleSpec (Var A) >>= ruleSpec (Var B)
    -- ⊢ S(B+A)=S(A+B)→A*B+S(B+A)=A*B+S(A+B)
    eq13' <- prop3 >>= ruleSpec (Var D) >>= ruleSpec (Plus (Var A) (S (Var B))) >>= ruleSpec (S (Plus (Var A) (Var B))) >>= ruleGeneralize D [premise] >>= ruleSpec (Mult (Var A) (Var B))
    -- ⊢ A*B+S(A+B)=A*B+A+SB
    eq13'' <- ruleDetachment eq13 eq13'
    eq13'' <- ruleSymmetry eq13''
    eq14 <- ruleTransitivity eq12 eq13''
    -- ⊢ A*B+A+SB=(A*B+A)+SB
    eq15 <- prop5 >>= ruleSpec (Var D) >>= ruleSpec (Var A) >>= ruleSpec (S (Var B)) >>= ruleGeneralize D [premise] >>= ruleSpec (Mult (Var A) (Var B))
    -- ⊢ SA*SB=(A*B+A)+SB
    eq16 <- ruleTransitivity eq14 eq15
    -- ⊢ A*SB=A*B+A
    eq17 <- axiom5 (Var A) (Var B) >>= ruleSpec (Var A) >>= ruleSpec (Var B)
    -- ⊢ A*SB=A*B+A→SB+A*SB=SB+A*B+A
    eq17' <- prop3 >>= ruleSpec (Var D) >>= ruleSpec (Mult (Var A) (S (Var B))) >>= ruleSpec (Plus (Mult (Var A) (Var B)) (Var A)) >>= ruleGeneralize D [premise] >>= ruleSpec (S (Var B))
    -- ⊢ SB+A*SB=SB+A*B+A
    eq17'' <- ruleDetachment eq17 eq17'
    -- ⊢ SB+A*B+A=(A*B+A)+SB
    eq17''' <- prop4 >>= ruleSpec (Var D) >>= ruleSpec (Plus (Mult (Var A) (Var B)) (Var A)) >>= ruleGeneralize D [premise] >>= ruleSpec (S (Var B))
    eq17'''' <- ruleTransitivity eq17'' eq17'''
    eq17'''' <- ruleSymmetry eq17''''
    -- ⊢ SA*SB=SB+A*SB
    eq18 <- ruleTransitivity eq16 eq17''''
    -- ⊢ SB+A*SB=A*SB+SB
    eq19 <- prop4 >>= ruleSpec (Var D) >>= ruleSpec (Mult (Var A) (S (Var B))) >>= ruleGeneralize D [premise] >>= ruleSpec (S (Var B))
    ruleTransitivity eq18 eq19
  ruleGeneralize B [] imp

-- ⊢ ∀A:∀B:(SA*B=A*B+B)
prop7 = join (ruleInduction <$> prop7base <*> prop7hyp) >>=  ruleGeneralize A []

{- Prop8 -}
-- ⊢ A*0=0*A
prop8base = do
  prop6 <- prop6
  ax4 <- axiom4 (Var A)
  eq1 <- ruleSpec (Var A) ax4
  eq2 <- ruleSpec (Var A) prop6
  eq2 <- ruleSymmetry eq2
  ruleTransitivity eq1 eq2

-- ⊢ ∀B:<A*B=B*A→A*SB=SB*A>
prop8hyp = do
  imp <- ruleFantasy (PropVar (Eq (Mult (Var A) (Var B)) (Mult (Var B) (Var A)))) $ \premise -> do
    -- ⊢ A*SB=A*B+A
    eq1 <- axiom5 (Var A) (Var B) >>= ruleSpec (Var A) >>= ruleSpec (Var B)
    -- ⊢ A*B=B*A→A+A*B=A+B*A
    eq2 <- prop3 >>= ruleSpec (Var A) >>= ruleSpec (Mult (Var A) (Var B)) >>= ruleSpec (Mult (Var B) (Var A))
    -- ⊢ A+A*B=A+B*A
    eq2' <- ruleDetachment premise eq2
    -- ⊢ A*B+A=A+A*B
    eq3 <- prop4 >>= ruleSpec (Var D) >>= ruleSpec (Var A) >>= ruleGeneralize D [premise] >>= ruleSpec (Mult (Var A) (Var B))
    -- ⊢ A*SB=A+A*B
    eq4 <- ruleTransitivity eq1 eq3
    -- ⊢ A*SB=A+B*A
    eq5 <- ruleTransitivity eq4 eq2'
    -- ⊢ A+B*A=B*A+A
    eq6 <- prop4 >>= ruleSpec (Var D) >>= ruleSpec (Var A) >>= ruleGeneralize D [premise] >>= ruleSpec (Mult (Var B) (Var A))
    eq6 <- ruleSymmetry eq6
    -- ⊢ A*SB=B*A+A
    eq7 <- ruleTransitivity eq5 eq6
    -- ⊢ B*A+A=SB*A
    eq8 <- prop7 >>= ruleSpec (Var D) >>= ruleSpec (Var A) >>= ruleGeneralize D [premise] >>= ruleSpec (Var B)
    eq8 <- ruleSymmetry eq8
    ruleTransitivity eq7 eq8
  ruleGeneralize B [] imp

-- ⊢ ∀A:∀B:(A*B=B*A)
prop8 = do
  eq1 <- join (ruleInduction <$> prop8base <*> prop8hyp)
  ruleGeneralize A [] eq1
