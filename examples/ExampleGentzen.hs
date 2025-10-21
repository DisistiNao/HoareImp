module ExampleGentzen where

import Common
import Control.Monad (join)
import ExampleCommon
import Gentzen
import PrettyPrinter
import TNT

main = do
  putStrLn "Session 1"
  mapM_ (putStrLn . pr) [s1prf1,s1prf2,s1prf3,s1prf3_2,s1prf4,s1prf5,s1prf6,s1prf7,s1prf7_2,s1prf8,s1prf9,s1prf10,s1prf10_2,s1prf10_3,s1prf11,s1prf12]
  putStrLn "Session 2"
  mapM_ (putStrLn . pr) [s2prf1,s2prf2,s2prf3,s2prf3,s2prf4,s2prf5,s2prf6,s2prf7,s2prf7,s2prf8,s2prf9,s2prf10,s2prf10,s2prf10,s2prf11,s2prf12,s2prf13,s2prf14]
  putStrLn "Session 3"
  mapM_ (putStrLn . pr) [s3prf1,s3prf2,s3prf3,s3prf3,s3prf4,s3prf5,s3prf6,s3prf7,s3prf7,s3prf8,s3prf9,s3prf10,s3prf10,s3prf10,s3prf11,s3prf12]
  putStrLn "Session 4"
  mapM_ (putStrLn . pr) [s4prf1,s4prf2,s4prf2_2,s4prf3,s4prf3,s4prf4,s4prf5,s4prf6,s4prf7,s4prf7,s4prf8,s4prf9,s4prf10,s4prf10,s4prf10,s4prf11,s4prf12,s4prf13,s4prf14,s4prf15]
  putStrLn "Hilbert system"
  mapM_ (putStrLn . pr) [hprf1,hprf2,hprf2,hprf3,hprf3,hprf4,hprf5,hprf6,hprf7,hprf7,hprf8,hprf9]

-- Helpers
-- x∧¬x
bottom x = And x (Not x)
-- ⊢ x∨¬x
exclMiddle x = ruleFantasy (Not x) Right >>= ruleSwitcheroo

-- ⊢ A∧<B∨C>→A∧<B∨¬¬C> without `applyPropRule`
eg = ruleFantasy (And (PropVar A) (Or (PropVar B) (PropVar C))) $ \premise -> do
  step1 <- s3lemma2' (PropVar B) (PropVar C)
  prfA <- ruleSepL premise
  prfBorC <- ruleSepR premise
  step2 <- ruleDetachment prfBorC step1
  step3 <- ruleSwitcheroo step2
  step4 <- ruleContra step3
  step5 <- ruleSwitcheroo step4
  ruleJoin prfA step5

-- Example proofs for exercises taken from http://incredible.pm/

-- | Session 1
-- ⊢ ¬<a→b>→a∧¬b
s1lemma1 a b = ruleFantasy (Not (Imp a b)) $ \premise -> do
   step1 <- applyPropRule [GoLeft,GoLeft] ruleDoubleTildeIntro premise
   step2 <- applyPropRule [GoLeft] ruleSwitcheroo step1
   step3 <- ruleDeMorgan step2
   applyPropRule [GoLeft] ruleDoubleTildeElim step3

-- ⊢ A→A
s1prf1 = ruleFantasy (PropVar (Var A)) Right
-- ⊢ A∧B→A
s1prf2 = ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) ruleSepL
-- ⊢ A∧B→B
s1prf3 = ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) ruleSepR
-- ⊢ A∧B→A
s1prf3_2 = ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) ruleSepL
-- ⊢ A∧B→A∧B
s1prf4 = ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) return
-- ⊢ A→A∧A
s1prf5 = ruleFantasy (PropVar (Var A)) (\prfA -> ruleJoin prfA prfA)
-- ⊢ A∧B→A
s1prf6 = ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) ruleSepL
-- ⊢ A∧B→A
s1prf7 = ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) ruleSepL
-- ⊢ A∧B→B
s1prf7_2 = ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) ruleSepR
-- ⊢ A∧B→A∧B
s1prf8 = ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) return
-- ⊢ A∧B→B∧A
s1prf9 = ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) (\prfAB -> join (ruleJoin <$> ruleSepR prfAB <*> ruleSepL prfAB))
-- ⊢ <A∧B→A>→<A∧B→B>→<B→A→B∧A>→A∧B→B∧A, tedious, but only relies on impl intro and impl elim
s1prf9' =
  ruleFantasy (Imp (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var A))) $ \premise1 -> do
    ruleFantasy (Imp (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var B))) $ \premise2 -> do
      ruleFantasy (Imp (PropVar (Var B)) (Imp (PropVar (Var A)) (And (PropVar (Var B)) (PropVar (Var A))))) $ \premise3 -> do
        ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) $ \premise4 -> do
          prfA <- ruleDetachment premise4 premise1
          prfB <- ruleDetachment premise4 premise2
          prf <- ruleDetachment prfB premise3
          ruleDetachment prfA prf
-- ⊢ <A∧B>∧C→A
s1prf10 = ruleFantasy (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C))) (\prfABC -> ruleSepL prfABC >>= ruleSepL)
-- ⊢ <A∧B>∧C→B
s1prf10_2 = ruleFantasy (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C))) (\prfABC -> ruleSepL prfABC >>= ruleSepR)
-- ⊢ <A∧B>∧C→C
s1prf10_3 = ruleFantasy (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C))) ruleSepR
-- ⊢ <A∧B>∧C→A∧C
s1prf11 = ruleFantasy (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C))) (\prfABC -> join (ruleJoin <$> join (ruleSepL <$> ruleSepL prfABC) <*> ruleSepR prfABC))
-- ⊢ <A∧B>∧C→A∧B∧C
s1prf12 = ruleFantasy (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C))) (\prfABC -> join (ruleJoin <$> join (ruleSepL <$> ruleSepL prfABC) <*> join (ruleJoin <$> join (ruleSepR <$> ruleSepL prfABC) <*> ruleSepR prfABC)))

-- | Session 2
-- ⊢ A∧<A→B>→B
s2prf1 = ruleFantasy (And (PropVar (Var A)) (Imp (PropVar (Var A)) (PropVar (Var B)))) (\prfAAtoB -> join (ruleDetachment <$> ruleSepL prfAAtoB <*> ruleSepR prfAAtoB))
-- ⊢ A∧<A→B>∧<B→C>→C
s2prf2 = ruleFantasy (And (PropVar (Var A)) (And (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var B)) (PropVar (Var C))))) $ \prfAAtoBAtoC -> do
  prfA <- ruleSepL prfAAtoBAtoC
  prfAtoB <- join $ ruleSepL <$> ruleSepR prfAAtoBAtoC
  prfBtoC <- join $ ruleSepR <$> ruleSepR prfAAtoBAtoC
  prfB <- ruleDetachment prfA prfAtoB
  ruleDetachment prfB prfBtoC
-- ⊢ A∧<<A→B>∧<B→D>>∧<A→C>∧<C→D>→D
s2prf3 = ruleFantasy (And (PropVar (Var A)) (And (And (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var B)) (PropVar (Var D)))) (And (Imp (PropVar (Var A)) (PropVar (Var C))) (Imp (PropVar (Var C)) (PropVar (Var D)))))) $ \premise -> do
  prfA <- ruleSepL premise
  prfAtoCCtoD <- join $ ruleSepR <$> ruleSepR premise
  prfAtoC <- ruleSepL prfAtoCCtoD
  prfCtoD <- ruleSepR prfAtoCCtoD
  prfC <- ruleDetachment prfA prfAtoC
  ruleDetachment prfC prfCtoD
-- ⊢ A→<A→A>→A
s2prf4 = ruleFantasy (PropVar (Var A)) $ \prfA -> do
  ruleFantasy (Imp (PropVar (Var A)) (PropVar (Var A))) (\prfAimpA -> ruleDetachment prfA prfAimpA)
-- ⊢ <A→B>∧<B→C>→A→C
s2prf5 = ruleFantasy (And (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var B)) (PropVar (Var C)))) $ \premise -> do
  prfAtoB <- ruleSepL premise
  prfBtoC <- ruleSepR premise
  ruleFantasy (PropVar (Var A)) $ \prfA -> do
    prfB <- ruleDetachment prfA prfAtoB
    ruleDetachment prfB prfBtoC
-- ⊢ <A→B>∧<A→B→C>→A→C
s2prf6 = ruleFantasy (And (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var A)) (Imp (PropVar (Var B)) (PropVar (Var C))))) $ \premise -> do
  prfAtoB <- ruleSepL premise
  prfAtoBtoC <- ruleSepR premise
  ruleFantasy (PropVar (Var A)) $ \prfA -> do
    prfB <- ruleDetachment prfA prfAtoB
    prfBtoC <- ruleDetachment prfA prfAtoBtoC
    ruleDetachment prfB prfBtoC
-- ⊢ A→A
s2prf7 = ruleFantasy (PropVar (Var A)) return
-- ⊢ <<A→C>∧<B→C>>∧A∧B→C
s2prf8 = ruleFantasy (And (And (Imp (PropVar (Var A)) (PropVar (Var C))) (Imp (PropVar (Var B)) (PropVar (Var C)))) (And (PropVar (Var A)) (PropVar (Var B)))) $ \premise -> do
  prfAtoCBtoC <- ruleSepL premise
  prfAtoC <- ruleSepL prfAtoCBtoC
  prfAB <- ruleSepR premise
  prfA <- ruleSepL prfAB
  ruleDetachment prfA prfAtoC
-- ⊢ <A→C>∧<B→C>→A∧B→C
s2prf9 = ruleFantasy (And (Imp (PropVar (Var A)) (PropVar (Var C))) (Imp (PropVar (Var B)) (PropVar (Var C)))) $ \premise -> do
  prfAtoC <- ruleSepL premise
  ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) $ \prfAB -> do
    prfA <- ruleSepL prfAB
    ruleDetachment prfA prfAtoC
-- ⊢ B→A→B
s2prf10 = ruleFantasy (PropVar (Var B)) (\prfB -> ruleFantasy (PropVar (Var A)) (\prfA -> return prfB))
-- ⊢ <A∧B→C>→A→B→C
s2prf11 = ruleFantasy (Imp (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C))) $ \prfAandBtoC -> do
  ruleFantasy (PropVar (Var A)) $ \prfA -> do
    ruleFantasy (PropVar (Var B)) $ \prfB -> do
      prfAandB <- ruleJoin prfA prfB
      ruleDetachment prfAandB prfAandBtoC
-- ⊢ <A→B→C>→A∧B→C
s2prf12 = ruleFantasy (Imp (PropVar (Var A)) (Imp (PropVar (Var B)) (PropVar (Var C)))) $ \prfAtoBtoC -> do
  ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) $ \prfAB -> do
    prfA <- ruleSepL prfAB
    prfB <- ruleSepR prfAB
    prfBtoC <- ruleDetachment prfA prfAtoBtoC
    ruleDetachment prfB prfBtoC
-- ⊢ <A→B>∧<A→C>→A→B∧C
s2prf13 = ruleFantasy (And (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var A)) (PropVar (Var C)))) $ \prfAtoBAtoC -> do
  ruleFantasy (PropVar (Var A)) $ \prfA -> do
    prfAtoB <- ruleSepL prfAtoBAtoC
    prfAtoC <- ruleSepR prfAtoBAtoC
    prfB <- ruleDetachment prfA prfAtoB
    prfC <- ruleDetachment prfA prfAtoC
    ruleJoin prfB prfC
-- ⊢ <A→A→B>∧<<A→B>→B>→B
s2prf14 = ruleFantasy (And (Imp (PropVar (Var A)) (Imp (PropVar (Var A)) (PropVar (Var B)))) (Imp (Imp (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var B)))) $ \premise -> do
   prfAtoAtoB <- ruleSepL premise
   prfAtoBtoA <- ruleSepR premise
   disjElim <- s3lemma3 (Imp (PropVar (Var A)) (PropVar (Var B))) (Not (Imp (PropVar (Var A)) (PropVar (Var B)))) (PropVar (Var B))
   excld <- exclMiddle (Imp (PropVar (Var A)) (PropVar (Var B)))
   p1 <- ruleFantasy (Imp (PropVar (Var A)) (PropVar (Var B))) (\prfAtoB -> ruleDetachment prfAtoB prfAtoBtoA)
   p2 <- ruleFantasy (Not (Imp (PropVar (Var A)) (PropVar (Var B)))) $ \prfnotAtoB -> do
     prfAnotB <- s1lemma1 (PropVar (Var A)) (PropVar (Var B))
     prfA <- ruleDetachment prfnotAtoB prfAnotB >>= ruleSepL
     ruleDetachment prfA prfAtoAtoB >>= ruleDetachment prfA
   p1andp2 <- ruleJoin p1 p2
   ruleDetachment p1andp2 disjElim >>= ruleDetachment excld

-- | Session 3
-- ⊢ x→x∨y
s3lemma1 x y = ruleFantasy x $ \premise -> do
  step1 <- ruleFantasy (Not x) $ \premise' -> do
    premise1 <- ruleJoin premise premise'
    premise2 <- s4lemma1 x y
    ruleDetachment premise1 premise2
  ruleSwitcheroo step1
-- ⊢ x∨y→y∨x
s3lemma2 x y = ruleFantasy (Or x y) $ \premise -> do
  step1 <- ruleSwitcheroo premise
  step2 <- ruleContra step1
  step3 <- ruleSwitcheroo step2
  applyPropRule [GoRight] ruleDoubleTildeElim step3
-- Also possible without `applyPropRule`, though if `y` is in the form of `(Not <..>)` the proof fails
s3lemma2' x y = ruleFantasy (Or x y) $ \premise -> do
  step1 <- ruleSwitcheroo premise
  step2 <- ruleContra step1
  step3 <- ruleFantasy (Not y) $ \premise2 -> do
    step4 <- ruleDetachment premise2 step2
    ruleDoubleTildeElim step4
  ruleSwitcheroo step3
-- ⊢ <a→c>∧<b→c>→a∨b→c
s3lemma3 a b c = ruleFantasy (And (Imp a c) (Imp b c)) $ \premise -> do
  ruleFantasy (Or a b) $ \prfAorB -> do
    prfAimpC <- ruleSepL premise
    prfBimpC <- ruleSepR premise
    prfCornotC <- exclMiddle c
    prfnotAtoB <- ruleSwitcheroo prfAorB
    prfnotCtoBottom <- ruleFantasy (Not c) $ \premise' -> do
      prfnotA <- ruleContra prfAimpC >>= ruleDetachment premise'
      prfB <- ruleSwitcheroo prfAorB >>= ruleDetachment prfnotA
      prfC <- ruleDetachment prfB prfBimpC
      ruleJoin premise' prfC
    prfnotCtoBottom'  <- applyPropRule [GoRight,GoRight] ruleDoubleTildeIntro prfnotCtoBottom
    prfnotCtoBottom'' <- applyPropRule [GoRight] ruleDeMorgan prfnotCtoBottom'
    prfCornotCtoC     <- ruleContra prfnotCtoBottom''
    ruleDetachment prfCornotC prfCornotCtoC
-- ⊢ <<a→d>∧<b→d>>∧<c→d>→<a∨b>∨c→d
s3lemma3_2 a b c d = ruleFantasy (And (And (Imp a d) (Imp b d)) (Imp c d)) $ \premise -> do
  ruleFantasy (Or (Or a b) c) $ \prfAorBorC -> do
    prfAimpD <- ruleSepL premise >>= ruleSepL
    prfBimpD <- ruleSepL premise >>= ruleSepR
    prfCimpD <- ruleSepR premise
    prfBornotB <- exclMiddle b
    -- ¬<A∨B>→C
    prfnotAorBtoC <- ruleSwitcheroo prfAorBorC
    -- ¬<¬A→B>→C
    prfnotnotAtoBtoC <- applyPropRule [GoLeft,GoLeft] ruleSwitcheroo prfnotAorBtoC
    -- ¬C→¬¬<¬A→B>
    prfnotCtonotAtoB <- ruleContra prfnotnotAtoBtoC >>= applyPropRule [GoRight] ruleDoubleTildeElim
    prfnotDtoBottom <- ruleFantasy (Not d) $ \premise' -> do
      prfnotA <- ruleContra prfAimpD >>= ruleDetachment premise'
      prfnotB <- ruleContra prfBimpD >>= ruleDetachment premise'
      prfnotC <- ruleContra prfCimpD >>= ruleDetachment premise'
      prfnotAtoB <- ruleDetachment prfnotC prfnotCtonotAtoB
      prfB <- ruleDetachment prfnotA prfnotAtoB
      ruleJoin prfB prfnotB
    prfnotDtoBottom'  <- applyPropRule [GoRight,GoLeft] ruleDoubleTildeIntro prfnotDtoBottom
    prfnotDtoBottom'' <- applyPropRule [GoRight] ruleDeMorgan prfnotDtoBottom'
    prfnotBorBtoD     <- ruleContra prfnotDtoBottom''
    prfs3lemma2       <- s3lemma2 (Not b) b
    prfBornotBtoD     <- applyPropRule [GoLeft] (\f -> ruleDetachment f prfs3lemma2) prfnotBorBtoD
    ruleDetachment prfBornotB prfBornotBtoD
-- ⊢ <a∨b→c>→<a→c>∧<b→c>
s3lemma4 a b c = ruleFantasy (Imp (Or a b) c) $ \prfAorBimpC -> do
  step1 <- applyPropRule [GoLeft] ruleDoubleTildeIntro prfAorBimpC
  step2 <- applyPropRule [GoLeft,GoLeft] ruleDeMorgan step1
  prfnotAandnotBorC <- ruleSwitcheroo step2
  prf <- s3lemma3 (And (Not a) (Not b)) c (And (Imp a c) (Imp b c))
  prf1 <- ruleFantasy (And (Not a) (Not b)) $ \prfnotAandnotB -> do
    prfnotA <- ruleSepL prfnotAandnotB
    prfnotB <- ruleSepR prfnotAandnotB
    prfnotCimpnotA <- ruleFantasy (Not c) (\_ -> return prfnotA)
    prfnotBimpnotA <- ruleFantasy (Not c) (\_ -> return prfnotB)
    prfAimpC <- ruleContra prfnotCimpnotA
    prfBimpC <- ruleContra prfnotBimpnotA
    ruleJoin prfAimpC prfBimpC
  prf2 <- ruleFantasy c $ \prfC -> do
    prfCAimpC <- ruleFantasy a (\_ -> return prfC)
    prfCBimpC <- ruleFantasy b (\_ -> return prfC)
    ruleJoin prfCAimpC prfCBimpC
  joined <- ruleJoin prf1 prf2
  ruleDetachment joined prf >>= ruleDetachment prfnotAandnotBorC

-- ⊢ A∧B→A∨B
s3prf1 = ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) $ \prfAB -> do
  prfA <- ruleSepL prfAB
  lemma <- s3lemma1 (PropVar (Var A)) (PropVar (Var B))
  ruleDetachment prfA lemma
-- ⊢ A→A∨B
s3prf2 = s3lemma1 (PropVar $ Var A) (PropVar $ Var B)
-- ⊢ B→A∨B
s3prf3 = ruleFantasy (PropVar $ Var B) $ \prfB -> do
  lemma1 <- s3lemma1 (PropVar $ Var B) (PropVar $ Var A)
  lemma2 <- s3lemma2 (PropVar $ Var B) (PropVar $ Var A)
  step1 <- ruleDetachment prfB lemma1
  ruleDetachment step1 lemma2
--  applyPropRule [GoRight] (\prf -> ruleDetachment prf lemma2) lemma1
-- ⊢ A→A∨A
s3prf4 = s3lemma1 (PropVar $ Var A) (PropVar $ Var A)
-- ⊢ A∨B→B∨A
s3prf5 = s3lemma2 (PropVar $ Var A) (PropVar $ Var B)
-- ⊢ A∨B∨C→<A∨B>∨C
s3prf6 = ruleFantasy (Or (PropVar (Var A)) (Or (PropVar (Var B)) (PropVar (Var C)))) $ \prfAorBorC -> do
  prf <- s3lemma3 (PropVar $ Var A) (Or (PropVar $ Var B) (PropVar $ Var C)) (Or (Or (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
  prf1 <- ruleFantasy (PropVar $ Var A) $ \prfA -> do
    lemma1 <- s3lemma1 (PropVar $ Var A) (PropVar $ Var B)
    lemma2 <- s3lemma1 (Or (PropVar $ Var A) (PropVar $ Var B)) (PropVar $ Var C)
    prfAorB <- ruleDetachment prfA lemma1
    ruleDetachment prfAorB lemma2
  prf2 <- ruleFantasy (Or (PropVar $ Var B) (PropVar $ Var C)) $ \prfBorC -> do
    prf' <- s3lemma3 (PropVar $ Var B) (PropVar $ Var C) (Or (Or (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
    prf1 <- ruleFantasy (PropVar $ Var B) $ \prfB -> do
      lemma1 <- s3lemma1 (PropVar $ Var B) (PropVar $ Var A)
      lemma2 <- s3lemma2 (PropVar $ Var B) (PropVar $ Var A)
      lemma3 <- s3lemma1 (Or (PropVar $ Var A) (PropVar $ Var B)) (PropVar $ Var C)
      prfBorA <- ruleDetachment prfB lemma1
      prfAorB <- ruleDetachment prfBorA lemma2
      ruleDetachment prfAorB lemma3
    prf2 <- ruleFantasy (PropVar $ Var C) $ \prfC -> do
      lemma1 <- s3lemma1 (PropVar $ Var C) (Or (PropVar $ Var A) (PropVar $ Var B))
      lemma2 <- s3lemma2 (PropVar $ Var C) (Or (PropVar $ Var A) (PropVar $ Var B))
      prfCorAorB <- ruleDetachment prfC lemma1
      ruleDetachment prfCorAorB lemma2
    joined <- ruleJoin prf1 prf2
    ruleDetachment joined prf' >>= ruleDetachment prfBorC
  joined <- ruleJoin prf1 prf2
  ruleDetachment joined prf >>= ruleDetachment prfAorBorC
-- ⊢ A∧B→A∨B
s3prf7 = s3prf1
-- ⊢ A∧B∨C→<A∨C>∧<B∨C>
s3prf8 = ruleFantasy (Or (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C))) $ \prfAandBorC -> do
  prf <- s3lemma3 (And (PropVar $ Var A) (PropVar $ Var B)) (PropVar $ Var C) (And (Or (PropVar (Var A)) (PropVar (Var C))) (Or (PropVar (Var B)) (PropVar (Var C))))
  prf1 <- ruleFantasy (And (PropVar $ Var A) (PropVar $ Var B)) $ \prfAandB -> do
    lemma1 <- s3lemma1 (PropVar $ Var A) (PropVar $ Var C)
    lemma2 <- s3lemma1 (PropVar $ Var B) (PropVar $ Var C)
    prfA <- ruleSepL prfAandB
    prfB <- ruleSepR prfAandB
    prfAorC <- ruleDetachment prfA lemma1
    prfBorC <- ruleDetachment prfB lemma2
    ruleJoin prfAorC prfBorC
  prf2 <- ruleFantasy (PropVar $ Var C) $ \prfC -> do
    lemma1 <- s3lemma1 (PropVar $ Var C) (PropVar $ Var A)
    lemma2 <- s3lemma1 (PropVar $ Var C) (PropVar $ Var B)
    lemma3 <- s3lemma2 (PropVar $ Var C) (PropVar $ Var A)
    lemma4 <- s3lemma2 (PropVar $ Var C) (PropVar $ Var B)
    prfCorA <- ruleDetachment prfC lemma1
    prfCorB <- ruleDetachment prfC lemma2
    prfAorC <- ruleDetachment prfCorA lemma3
    prfBorC <- ruleDetachment prfCorB lemma4
    ruleJoin prfAorC prfBorC
  joined <- ruleJoin prf1 prf2
  ruleDetachment joined prf >>= ruleDetachment prfAandBorC
-- ⊢ <A∨B>∧C→A∧C∨B∧C
s3prf9 = ruleFantasy (And (Or (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C))) $ \prfAorBandC -> do
  prfAorB <- ruleSepL prfAorBandC
  prfC    <- ruleSepR prfAorBandC
  prf     <- s3lemma3 (PropVar $ Var A) (PropVar $ Var B) (Or (And (PropVar (Var A)) (PropVar (Var C))) (And (PropVar (Var B)) (PropVar (Var C))))
  prf1    <- ruleFantasy (PropVar $ Var A) $ \prfA -> do
    lemma <- s3lemma1 (And (PropVar $ Var A) (PropVar $ Var C)) (And (PropVar $ Var B) (PropVar $ Var C))
    prfAandC <- ruleJoin prfA prfC
    ruleDetachment prfAandC lemma
  prf2    <- ruleFantasy (PropVar $ Var B) $ \prfB -> do
    lemma1 <- s3lemma1 (And (PropVar $ Var B) (PropVar $ Var C)) (And (PropVar $ Var A) (PropVar $ Var C))
    lemma2 <- s3lemma2 (And (PropVar $ Var B) (PropVar $ Var C)) (And (PropVar $ Var A) (PropVar $ Var C))
    prfBandC <- ruleJoin prfB prfC
    prfBandCorAandC <- ruleDetachment prfBandC lemma1
    ruleDetachment prfBandCorAandC lemma2
  joined <- ruleJoin prf1 prf2
  ruleDetachment joined prf >>= ruleDetachment prfAorB
-- ⊢ <A→C>∧<B→C>→A∨B→C
s3prf10 = s3lemma3 (PropVar $ Var A) (PropVar $ Var B) (PropVar $ Var C)
-- ⊢ <A∨B→C>→<A→C>∧<B→C>
s3prf11 = s3lemma4 (PropVar (Var A)) (PropVar (Var B)) (PropVar (Var C))
-- ⊢ <A→B>∨<A→C>→A→B∨C
s3prf12 = ruleFantasy (Or (Imp (PropVar $ Var A) (PropVar $ Var B)) (Imp (PropVar $ Var A) (PropVar $ Var C))) $ \prfAimpBorAimpC -> do
  ruleFantasy (PropVar (Var A)) $ \prfA -> do
    prf <- s3lemma3 (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var A)) (PropVar (Var C))) (Imp (PropVar (Var A)) (Or (PropVar (Var B)) (PropVar (Var C))))
    prf1 <- ruleFantasy (Imp (PropVar (Var A)) (PropVar (Var B))) $ \prfAimpB -> do
      lemma1 <- s3lemma1 (PropVar (Var B)) (PropVar (Var C))
      prfB <- ruleDetachment prfA prfAimpB
      prfBorC <- ruleDetachment prfB lemma1
      ruleFantasy (PropVar (Var A)) (\_ -> return prfBorC)
    prf2 <- ruleFantasy (Imp (PropVar (Var A)) (PropVar (Var C))) $ \prfAimpC -> do
      lemma1 <- s3lemma1 (PropVar (Var C)) (PropVar (Var B))
      lemma2 <- s3lemma2 (PropVar $ Var C) (PropVar $ Var B)
      prfC <- ruleDetachment prfA prfAimpC
      prfCorB <- ruleDetachment prfC lemma1
      prfBorC <- ruleDetachment prfCorB lemma2
      ruleFantasy (PropVar (Var A)) (\_ -> return prfBorC)
    joined <- ruleJoin prf1 prf2
    ruleDetachment joined prf >>= ruleDetachment prfAimpBorAimpC >>= ruleDetachment prfA

-- | Session 4
-- The following identity is used: E∧¬E = bottom

-- ⊢ x∧¬x→y
s4lemma1 x y = ruleFantasy (bottom x) $ \premise -> do
  left <- ruleSepL premise
  right <- ruleSepR premise
  prfImp <- do
    step1 <- ruleFantasy (Not y) (return $ ruleDoubleTildeIntro left)
    ruleContra step1
  ruleDetachment right prfImp
-- ⊢ x∨(x→Bottom)
s4lemma2 x = do
  prfAornotA <- exclMiddle x
  prf <- s3lemma3 x (Not x) (Or x (Imp x (bottom (PropVar (Var E)))))
  prf1 <- s3lemma1 x (Imp x (bottom (PropVar (Var E))))
  prf2 <- ruleFantasy (Not x) $ \prfNotx -> do
    prfAtoBottom <- ruleFantasy x $ \prfx -> do
      lemma1 <- s4lemma1 x (bottom (PropVar (Var E)))
      joined <- ruleJoin prfx prfNotx
      ruleDetachment joined lemma1
    lemma1 <- s3lemma1 (Imp x (bottom (PropVar (Var E)))) x
    lemma2 <- s3lemma2 (Imp x (bottom (PropVar (Var E)))) x
    prfAtoBottomorA <- ruleDetachment prfAtoBottom lemma1
    ruleDetachment prfAtoBottomorA lemma2
  joined <- ruleJoin prf1 prf2
  ruleDetachment joined prf >>= ruleDetachment prfAornotA

-- ⊢ E∧¬E→A
s4prf1 = s4lemma1 (PropVar $ Var E) (PropVar $ Var A)
-- ⊢ E∧¬E→A
s4prf2 = s4lemma1 (PropVar $ Var E) (PropVar $ Var A)
-- ⊢ E∧¬E→B
s4prf2_2 = s4lemma1 (PropVar $ Var E) (PropVar $ Var B)
-- ⊢ A→E∧¬E∨A
s4prf3 = do
  lemma1 <- s3lemma1 (PropVar (Var A)) (bottom (PropVar (Var E)))
  let rule = \prf -> do
        lemma2 <- s3lemma2 (PropVar (Var A)) (bottom (PropVar (Var E)))
        ruleDetachment prf lemma2
  applyPropRule [GoRight] rule lemma1
-- ⊢ E∧¬E∨A→A
s4prf4 = ruleFantasy (Or (bottom (PropVar (Var E))) (PropVar (Var A))) $ \prfBottomorA -> do
  lemma1 <- s3lemma3 (bottom (PropVar (Var E))) (PropVar (Var A)) (PropVar (Var A))
  prfBottomtoA <- s4lemma1 (PropVar (Var E)) (PropVar (Var A))
  prf1 <- ruleFantasy (bottom (PropVar (Var E))) (\x -> ruleDetachment x prfBottomtoA)
  prf2 <- ruleFantasy (PropVar (Var A)) return
  joined <- ruleJoin prf1 prf2
  ruleDetachment joined lemma1 >>= ruleDetachment prfBottomorA
-- ⊢ <E∧¬E>∧A→E∧¬E
s4prf5 = ruleFantasy (And (bottom (PropVar (Var E))) (PropVar (Var A))) ruleSepL
-- ⊢ E∧¬E→A
s4prf6 = s4prf1
-- ⊢ <A→B>→<B→E∧¬E>→A→E∧¬E
s4prf7 = ruleFantasy (Imp (PropVar (Var A)) (PropVar (Var B))) $ \prfAtoB ->
  ruleFantasy (Imp (PropVar (Var B)) (bottom (PropVar (Var E)))) $ \prfBtoBottom ->
    ruleFantasy (PropVar (Var A)) $ \prfA -> do
      prfB <- ruleDetachment prfA prfAtoB
      ruleDetachment prfB prfBtoBottom
-- ⊢ <A∨B→E∧¬E>→<A→E∧¬E>∧<B→E∧¬E>
s4prf8 = s3lemma4 (PropVar (Var A)) (PropVar (Var B)) (bottom (PropVar (Var E)))
-- ⊢ <A→E∧¬E>∧<B→E∧¬E>→A∨B→E∧¬E
s4prf9 = s3lemma3 (PropVar (Var A)) (PropVar (Var B)) (bottom (PropVar (Var E)))
-- ⊢ <A→E∧¬E>∨<B→E∧¬E>→A∧B→E∧¬E
s4prf10 = ruleFantasy (Or (Imp (PropVar (Var A)) (bottom (PropVar (Var E)))) (Imp (PropVar (Var B)) (bottom (PropVar (Var E))))) $ \prfAimpBottomorBimpBottom -> do
  prf <- s3lemma3 (Imp (PropVar (Var A)) (bottom (PropVar (Var E)))) (Imp (PropVar (Var B)) (bottom (PropVar (Var E)))) (Imp (And (PropVar (Var A)) (PropVar (Var B))) (bottom (PropVar (Var E))))
  prf1 <- ruleFantasy (Imp (PropVar (Var A)) (bottom (PropVar (Var E)))) $ \prfAimpBottom ->
    ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) $ \prfAB -> do
      prfA <- ruleSepL prfAB
      ruleDetachment prfA prfAimpBottom
  prf2 <- ruleFantasy (Imp (PropVar (Var B)) (bottom (PropVar (Var E)))) $ \prfBimpBottom ->
    ruleFantasy (And (PropVar (Var A)) (PropVar (Var B))) $ \prfAB -> do
      prfB <- ruleSepR prfAB
      ruleDetachment prfB prfBimpBottom
  joined <- ruleJoin prf1 prf2
  ruleDetachment joined prf >>= ruleDetachment prfAimpBottomorBimpBottom
-- ⊢ <<<A→E∧¬E>→E∧¬E>→E∧¬E>→A→E∧¬E
s4prf11 = ruleFantasy (Imp (Imp (Imp (PropVar (Var A)) (bottom (PropVar (Var E)))) (bottom (PropVar (Var E)))) (bottom (PropVar (Var E)))) $ \imp ->
  ruleFantasy (PropVar (Var A)) $ \prfA -> do
    prfAtoBottomtoBottom <- ruleFantasy (Imp (PropVar (Var A)) (bottom (PropVar (Var E)))) (ruleDetachment prfA)
    ruleDetachment prfAtoBottomtoBottom imp
-- ⊢ <A→E∧¬E>∨B→A→B
s4prf12 = ruleFantasy (Or (Imp (PropVar (Var A)) (bottom (PropVar (Var E)))) (PropVar (Var B))) $ \prfAtoBottomorB ->
  ruleFantasy (PropVar (Var A)) $ \prfA -> do
    prf <- s3lemma3 (Imp (PropVar (Var A)) (bottom (PropVar (Var E)))) (PropVar (Var B)) (PropVar (Var B))
    prf1 <- ruleFantasy (Imp (PropVar (Var A)) (bottom (PropVar (Var E)))) $ \prfAtoBottom -> do
      lemma1 <- s4lemma1 (PropVar $ Var E) (PropVar $ Var B)
      prf1 <- ruleDetachment prfA prfAtoBottom
      ruleDetachment prf1 lemma1
    prf2 <- ruleFantasy (PropVar (Var B)) return
    joined <- ruleJoin prf1 prf2
    ruleDetachment joined prf >>= ruleDetachment prfAtoBottomorB
-- ⊢ <A→E∧¬E>∧<B→A>→B→E∧¬E
s4prf13 = ruleFantasy (And (Imp (PropVar (Var A)) (bottom (PropVar (Var E)))) (Imp (PropVar (Var B)) (PropVar (Var A)))) $ \prfAtoBottomBtoA ->
  ruleFantasy (PropVar (Var B)) $ \prfB -> do
    prfAtoBottom <- ruleSepL prfAtoBottomBtoA
    prfBtoA      <- ruleSepR prfAtoBottomBtoA
    prfA <- ruleDetachment prfB prfBtoA
    ruleDetachment prfA prfAtoBottom
-- ⊢ <<A→E∧¬E>∨<B→E∧¬E>>∨<C→E∧¬E>→<A∧B>∧C→E∧¬E
s4prf14 = ruleFantasy (Or (Or (Imp (PropVar (Var A)) (bottom (PropVar (Var E)))) (Imp (PropVar (Var B)) (bottom (PropVar (Var E))))) (Imp (PropVar (Var C)) (bottom (PropVar (Var E))))) $ \prfAimpBottomorBimpBottom -> do
  prf <- s3lemma3_2 (Imp (PropVar (Var A)) (bottom (PropVar (Var E)))) (Imp (PropVar (Var B)) (bottom (PropVar (Var E)))) (Imp (PropVar (Var C)) (bottom (PropVar (Var E)))) (Imp (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C))) (bottom (PropVar (Var E))))
  prf1 <- ruleFantasy (Imp (PropVar (Var A)) (bottom (PropVar (Var E)))) $ \prfAimpBottom ->
    ruleFantasy (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C))) $ \prfABC -> do
      prfA <- join $ ruleSepL <$> ruleSepL prfABC
      ruleDetachment prfA prfAimpBottom
  prf2 <- ruleFantasy (Imp (PropVar (Var B)) (bottom (PropVar (Var E)))) $ \prfBimpBottom ->
    ruleFantasy (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C))) $ \prfABC -> do
      prfB <- join $ ruleSepR <$> ruleSepL prfABC
      ruleDetachment prfB prfBimpBottom
  prf3 <- ruleFantasy (Imp (PropVar (Var C)) (bottom (PropVar (Var E)))) $ \prfBimpBottom ->
    ruleFantasy (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C))) $ \prfABC -> do
      prfB <- ruleSepR prfABC
      ruleDetachment prfB prfBimpBottom
  joined <- ruleJoin prf1 prf2
  joined <- ruleJoin joined prf3
  ruleDetachment joined prf >>= ruleDetachment prfAimpBottomorBimpBottom
-- ⊢ <A∨<A→E∧¬E>→E∧¬E>→E∧¬E
s4prf15 = ruleFantasy (Imp (Or (PropVar (Var A)) (Imp (PropVar (Var A)) (bottom (PropVar (Var E))))) (bottom (PropVar (Var E)))) $ \prfAorAtoBottomtoBottom -> do
  lemma1 <- s4lemma2 (PropVar (Var A))
  ruleDetachment lemma1 prfAorAtoBottomtoBottom

-- | Hilbert system
-- ⊢ a∨a→a
hlemma1 a = ruleFantasy (Or a a) $ \prfAorA -> do
  lemma1 <- s3lemma3 a a a
  prfAtoA <- ruleFantasy (PropVar (Var A)) return
  joined <- ruleJoin prfAtoA prfAtoA
  ruleDetachment joined lemma1 >>= ruleDetachment prfAorA

-- ⊢ A→A
hprf1 = ruleFantasy (PropVar (Var A)) return
-- ⊢ <B→C>→<A→B>→A→C
hprf2 = ruleFantasy (Imp (PropVar (Var B)) (PropVar (Var C))) $ \prfBtoC ->
  ruleFantasy (Imp (PropVar (Var A)) (PropVar (Var B))) $ \prfAtoB ->
    ruleFantasy (PropVar (Var A)) $ \prfA -> do
      prfB <- ruleDetachment prfA prfAtoB
      ruleDetachment prfB prfBtoC
-- ⊢ <A→B→C>→B→A→C
hprf3 = ruleFantasy (Imp (PropVar (Var A)) (Imp (PropVar (Var B)) (PropVar (Var C)))) $ \prfAtoBtoC ->
  ruleFantasy (PropVar (Var B)) $ \prfB ->
    ruleFantasy (PropVar (Var A)) $ \prfA -> do
      prfBtoC <- ruleDetachment prfA prfAtoBtoC
      ruleDetachment prfB prfBtoC
-- ⊢ ¬A→A→B
hprf4 = ruleFantasy (Not (PropVar (Var A))) $ \prfnotA ->
  ruleFantasy (PropVar (Var A)) $ \prfA -> do
    lemma1 <- s4lemma1 (PropVar (Var A)) (PropVar (Var B))
    joined <- ruleJoin prfA prfnotA
    ruleDetachment joined lemma1
-- ⊢ <¬A→A>→A
hprf5 = ruleFantasy (Imp (Not (PropVar (Var A))) (PropVar (Var A))) $ \prfnotAtoB -> do
  lemma1 <- hlemma1 (PropVar (Var A))
  prfAorA <- ruleSwitcheroo prfnotAtoB
  ruleDetachment prfAorA lemma1
-- ⊢ ¬¬A→A
hprf6 = ruleFantasy (Not (Not (PropVar (Var A)))) ruleDoubleTildeElim
-- ⊢ A→¬¬A
hprf7 = ruleFantasy (PropVar (Var A)) ruleDoubleTildeIntro
-- ⊢ <B→A>→¬A→¬B
hprf8 = ruleFantasy (Imp (PropVar (Var B)) (PropVar (Var A))) ruleContra
-- ⊢ <A→B>→<¬A→B>→B
hprf9 = ruleFantasy (Imp (PropVar (Var A)) (PropVar (Var B))) $ \prfAtoB ->
  ruleFantasy (Imp (Not (PropVar (Var A))) (PropVar (Var B))) $ \prfnotAtoB -> do
   lemma1 <- s3lemma3 (PropVar $ Var A) (Not (PropVar $ Var A)) (PropVar (Var B))
   prfAornotA <- exclMiddle (PropVar (Var A))
   joined <- ruleJoin prfAtoB prfnotAtoB
   ruleDetachment joined lemma1 >>= ruleDetachment prfAornotA
