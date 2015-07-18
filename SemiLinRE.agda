module SemiLinRE where

open import Data.Vec
open import Data.Nat
import Data.Fin as Fin

open import Data.List
import Data.List.All
open import Data.Bool
open import Data.Char

open import Data.Maybe

open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.Core

open import Category.Monad

open import Data.Nat.Properties.Simple

open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utils

open import Function

import RETypes

open import Data.Sum

open import SemiLin

open import Data.Vec.Equality
open import Data.Nat.Properties.Simple


module VecNatEq = Data.Vec.Equality.DecidableEquality (Relation.Binary.PropositionalEquality.decSetoid Data.Nat._≟_)



testPf : {n : ℕ} (sh : LinSet n) (su : SemiLinSet n) (sv : SemiLinSet n) -> (sh ∷ su ) +s sv ≡ (Data.List.map (λ x → sh +l x) sv ) Data.List.++ (su +s sv)
testPf sh su sv = refl
{-
  begin 
    (sh ∷ su) +s sv 
    ≡⟨ refl ⟩ 
    Data.List.concat
      (Data.List.map (λ l1 → Data.List.map (λ l2 → l1 +l l2) sv)
       (sh ∷ su)) 
    ≡⟨ refl ⟩ 
    Data.List.concat (Data.List.map (λ l2 → sh +l l2) sv ∷ Data.List.map (λ l1 → Data.List.map (λ l2 → l1 +l l2) sv) su) 
    ≡⟨ refl ⟩
    Data.List.map (λ l2 → sh +l l2) sv Data.List.++ Data.List.concat (Data.List.map (λ l1 → Data.List.map (λ l2 → l1 +l l2) sv) su) 
    ≡⟨ refl ⟩ 
    Data.List.map (λ l2 → sh +l l2) sv Data.List.++ su +s sv 
    ∎ -}

baseSplit : {n : ℕ} (ub vb : Parikh n) (vm : ℕ) (vvecs : Vec (Parikh n) vm) (vconsts : Vec ℕ vm) -> 
  applyLinComb (ub +v vb) vm vvecs vconsts
  ≡ ub +v applyLinComb vb vm vvecs vconsts
baseSplit ub vb .0 [] [] = refl
baseSplit ub vb (suc m) (x ∷ vvecs) (c ∷ vconsts)  = 
  begin 
  applyLinComb (ub +v vb) (suc m) (x ∷ vvecs) (c ∷ vconsts) 
  ≡⟨ refl ⟩ --cong {!!} (baseSplit ub vb _ vvecs vconsts) 
  (c ·ₛ x) +v applyLinComb (ub +v vb) m vvecs vconsts 
  ≡⟨ cong (λ x₁ → (c ·ₛ x) +v x₁) (baseSplit ub vb m vvecs vconsts) ⟩ 
  (c ·ₛ x) +v (ub +v applyLinComb vb m vvecs vconsts) 
  ≡⟨ sym vAssoc ⟩ 
  ((c ·ₛ x) +v ub) +v applyLinComb vb m vvecs vconsts 
  ≡⟨ cong (λ x₁ → x₁ +v applyLinComb vb m vvecs vconsts) (v+-commut (c ·ₛ x) ub) ⟩ 
  (ub +v (c ·ₛ x)) +v applyLinComb vb m vvecs vconsts 
  ≡⟨ vAssoc ⟩ 
  (ub +v ((c ·ₛ x) +v applyLinComb vb m vvecs vconsts) ∎)


combSplit :
  {n : ℕ} (ub vb : Parikh n) (um vm : ℕ) (uvecs : Vec (Parikh n) um) (vvecs : Vec (Parikh n) vm) (uconsts : Vec ℕ um) (vconsts : Vec ℕ vm) -> 
  (applyLinComb (ub +v vb) (um + vm) (uvecs Data.Vec.++ vvecs) (uconsts Data.Vec.++ vconsts)
  ≡ (applyLinComb ub um uvecs uconsts) +v (applyLinComb vb vm vvecs vconsts) )
combSplit ub vb .0 vm [] vvecs [] vconsts = baseSplit ub vb vm vvecs vconsts
combSplit ub vb (suc um) vm (x ∷ uvecs) vvecs (uc ∷ uconsts) vconsts = 
  begin 
  applyLinComb (ub +v vb) (suc (um + vm))
    (x ∷ uvecs Data.Vec.++ vvecs) ((uc ∷ uconsts) Data.Vec.++ vconsts) 
  ≡⟨ refl ⟩ 
  (uc ·ₛ x) +v applyLinComb (ub +v vb) (um + vm) (uvecs Data.Vec.++ vvecs)
                 (uconsts Data.Vec.++ vconsts) 
  ≡⟨ cong (λ x₁ → (uc ·ₛ x) +v x₁) (combSplit ub vb um vm uvecs vvecs uconsts vconsts) ⟩ 
  (uc ·ₛ x) +v
    (applyLinComb ub um uvecs uconsts +v
     applyLinComb vb vm vvecs vconsts) 
  ≡⟨ sym vAssoc ⟩ 
  ((uc ·ₛ x) +v applyLinComb ub um uvecs uconsts) +v
    applyLinComb vb vm vvecs vconsts 
  ≡⟨ refl ⟩ 
  (((uc ·ₛ x) +v applyLinComb ub um uvecs uconsts) +v
     applyLinComb vb vm vvecs vconsts ∎)


--Stolen from the stdlib
listIdentity : {A : Set} -> (x : List A) -> (x Data.List.++ [] ) ≡ x
listIdentity [] = refl
listIdentity (x ∷ xs) = cong (_∷_ x) (listIdentity xs)


-- ? ≡⟨ ? ⟩ ?
sumPreserved : 
  {n : ℕ} 
  -> (u : Parikh n) 
  -> (v : Parikh n)
  -- -> (uv : Parikh n)
  -> (su : SemiLinSet n) 
  -> (sv : SemiLinSet n)
  -- -> (suv : SemiLinSet n)
  -- -> (uv ≡ u +v v)
  -- -> (suv ≡ su +s sv)
  -> InSemiLin u su
  -> InSemiLin v sv
  -> InSemiLin (u +v v) (su +s sv)
sumPreserved u v .((ub , um , uvecs) ∷ st) .((vb , vm , vvecs) ∷ st₁) (InHead .u (ub , um , uvecs) st (uconsts , upf)) (InHead .v (vb , vm , vvecs) st₁ (vconsts , vpf))
  rewrite   upf | vpf 
  = InHead (u +v v) (ub +v vb , um + vm , uvecs Data.Vec.++ vvecs) (Data.List.map (_+l_ (ub , um , uvecs)) st₁ Data.List.++
                                                                       Data.List.foldr Data.List._++_ []
                                                                       (Data.List.map
                                                                        (λ z → z +l (vb , vm , vvecs) ∷ Data.List.map (_+l_ z) st₁) st)) 
  ((uconsts Data.Vec.++ vconsts) , trans (combSplit ub vb um vm uvecs vvecs uconsts vconsts) 
  (sym (subst (λ x → u +v v ≡ x +v applyLinComb vb vm vvecs vconsts) (sym upf) (cong (λ x → u +v x) (sym vpf)))) )

sumPreserved u v .(sh ∷ st) .(sh₁ ∷ st₁) (InHead .u sh st x) (InTail .v sh₁ st₁ vIn) = 
  let
    subCall1 : InSemiLin (u +v v) ((sh ∷ []) +s  st₁)
    subCall1 = sumPreserved u v (sh ∷ []) ( st₁) (InHead u sh [] x) vIn
    

    eqTest : (sh ∷ []) +s ( st₁) ≡ Data.List.map (λ l2 → sh +l l2) st₁
    eqTest = 
      begin 
      (sh ∷ []) +s (st₁) 
      ≡⟨ refl ⟩ 
      Data.List.map (λ l2 → sh +l l2) ( st₁) Data.List.++ [] 
      ≡⟨ listIdentity (Data.List.map (_+l_ sh) st₁) ⟩ 
      Data.List.map (λ l2 → sh +l l2) (st₁) 
      ≡⟨ refl ⟩ 
      (Data.List.map (λ l2 → sh +l l2) st₁ ∎)
    
    newCall = slExtend (u +v v) (Data.List.map (_+l_ sh) st₁) (subst (InSemiLin (u +v v)) eqTest subCall1) (sh +l sh₁) -- 
  in slConcatRight (u +v v) (Data.List.map (λ l2 → sh +l l2) (sh₁ ∷ st₁)) newCall (Data.List.foldr Data.List._++_ []
                                                                                     (Data.List.map (λ z → z +l sh₁ ∷ Data.List.map (_+l_ z) st₁) st))
sumPreserved u v .(sh ∷ st) sv (InTail .u sh st uIn) vIn = 
  (slConcatLeft (u +v v) (st +s sv) (sumPreserved u v st sv uIn vIn) (Data.List.map (λ x → sh +l x) sv)) 


--The algorithm mapping regular expressions to the Parikh set of
--the language matched by the RE
--We prove this correct below
reSemiLin : {n : ℕ} {null? : RETypes.Null?} -> (Char -> Fin.Fin n) -> RETypes.RE null? -> SemiLinSet n 
reSemiLin cmap RETypes.ε = Data.List.[ v0 , 0 , [] ]
reSemiLin cmap RETypes.∅ = []
reSemiLin cmap (RETypes.Lit x) = Data.List.[ basis (cmap x ) , 0 , [] ]
reSemiLin cmap (r1 RETypes.+ r2) = reSemiLin cmap r1 Data.List.++ reSemiLin cmap r2
reSemiLin cmap (r1 RETypes.· r2) = reSemiLin cmap r1 +s reSemiLin cmap r2
reSemiLin cmap (r RETypes.*) = Data.List.[ concatLinSets ( reSemiLin cmap r)  ]


{-
--Used in the proof for star
--Given a semilinear set for r, and the semilinear set for r *,
--And a proof that a word's parikh is in the semilin for r
--Find a proof that the word's parikh is in the semilin for r* 
findConstMultMatch : {n : ℕ}
      -> (par : Parikh n )
      -> (sub : SemiLinSet n) 
      -> (top : LinSet n) 
      ->  (top ≡ concatLinSets sub )
      -> (proj₁ (proj₂ top ) ) ≡ Data.List.sum (Data.List.map (λ x -> suc (proj₁ (proj₂ x ) ) ) sub)
      -> InSemiLin par sub
      -> LinComb par top 
--findConstMultMatch par (sh ∷ st) (_ , 0 , []) () _
findConstMultMatch {n} par .(sh ∷ st) (tbase , tm ,  tVecs) mapPf sumPf (InHead .par sh st linComb) = 
  let
    (subCoeffs , subPf ) = linComb
    (sbase , sm , svec) = sh
    (_ , m2 , subVecs) = concatLinSets st

    tVecLength : tm ≡ (suc (sm) ) + m2
    tVecLength = cong (proj₁ ∘ proj₂) mapPf

    newTVecs : Vec (Parikh n) ((suc (sm) ) + m2)
    newTVecs = subst (Vec (Parikh n)) tVecLength tVecs

    newMapPf : ((tbase , tm ,  tVecs) ≡ concatLinSets (sh ∷ st) )
    newMapPf = mapPf
    
    currentTVecs : Vec (Parikh n) (suc (sm) )
    currentTVecs = Data.Vec.take (suc sm) newTVecs

    --takeEq : Data.Vec.take (suc sm) (sbase ∷ svec) ≡ (sbase ∷ svec)
    --takeEq = ?

    --startSame : currentTVecs ≡ sbase ∷ svec
    --startSame = cong (λ x → {!!}) newMapPf

  in {!!}
findConstMultMatch par .(sh ∷ st) (_ , tm , tVecs) mapPf sumPf (InTail .par sh st inHead) = {!!}
-}

scalarAssoc : {n : ℕ} -> (x y : ℕ ) -> (v : Parikh n) -> (x + y) ·ₛ v ≡  (x ·ₛ v) +v (y ·ₛ v)
scalarAssoc x y [] = refl
scalarAssoc x y (vfirst ∷ v) rewrite scalarAssoc x y v | distribʳ-*-+ vfirst x y = refl

applyCombSum : 
  {n m : ℕ} -> 
  (vecs : Vec (Parikh n) m ) ->
  (uconsts vconsts : Parikh m ) -> 
  applyLinComb v0 m vecs (uconsts +v vconsts) ≡ applyLinComb v0 m vecs uconsts +v applyLinComb v0 m vecs vconsts
applyCombSum [] uconsts vconsts = sym v0identRight
applyCombSum {n} {suc m} (firstVec ∷ vecs) (uc ∷ uconsts) (vc ∷ vconsts) rewrite applyCombSum vecs uconsts vconsts | scalarAssoc uc vc firstVec = 
  begin 
  ((uc ·ₛ firstVec) +v (vc ·ₛ firstVec)) +v
    (applyLinComb v0 m vecs uconsts +v
     applyLinComb v0 m vecs vconsts) 
  ≡⟨ vAssoc ⟩ 
  (uc ·ₛ firstVec) +v
    ((vc ·ₛ firstVec) +v
     (applyLinComb v0 m vecs uconsts +v
      applyLinComb v0 m vecs vconsts)) 
  ≡⟨ cong (λ x → (uc ·ₛ firstVec) +v x) (v+-commut (vc ·ₛ firstVec) (applyLinComb v0 m vecs uconsts +v applyLinComb v0 m vecs vconsts)) ⟩ 
  (uc ·ₛ firstVec) +v
    ((applyLinComb v0 m vecs uconsts +v applyLinComb v0 m vecs vconsts)
     +v (vc ·ₛ firstVec)) 
  ≡⟨ sym vAssoc ⟩ 
  ((uc ·ₛ firstVec) +v
     (applyLinComb v0 m vecs uconsts +v applyLinComb v0 m vecs vconsts))
    +v (vc ·ₛ firstVec) 
  ≡⟨ cong (λ x → x +v (vc ·ₛ firstVec)) (sym vAssoc) ⟩ 
  (((uc ·ₛ firstVec) +v applyLinComb v0 m vecs uconsts) +v
     applyLinComb v0 m vecs vconsts)
    +v (vc ·ₛ firstVec) 
  ≡⟨ vAssoc ⟩ 
  ((uc ·ₛ firstVec) +v applyLinComb v0 m vecs uconsts) +v
    (applyLinComb v0 m vecs vconsts +v (vc ·ₛ firstVec)) 
  ≡⟨ cong (λ x → ((uc ·ₛ firstVec) +v applyLinComb v0 m vecs uconsts) +v x) (v+-commut (applyLinComb v0 m vecs vconsts) (vc ·ₛ firstVec)) ⟩ 
  ((uc ·ₛ firstVec) +v applyLinComb v0 m vecs uconsts) +v
    ((vc ·ₛ firstVec) +v applyLinComb v0 m vecs vconsts) ∎
-- ? ≡⟨ ? ⟩ ?
--If a linear set has base 0, and u and v are both in that set, then u+v is as well
sumEqualVecs : {n : ℕ} -> (ls : LinSet n) -> (proj₁ ls ≡ v0) -> (u v : Parikh n) -> LinComb u ls -> LinComb v ls -> LinComb (u +v v) ls
sumEqualVecs (.v0 , m , vecs) refl .(applyLinComb v0 m vecs uconsts) .(applyLinComb v0 m vecs vconsts) (uconsts , refl) (vconsts , refl)  = 
  (uconsts +v vconsts) , applyCombSum vecs uconsts vconsts --applyCombSum {!!} {!!} vecs uconsts vconsts

rightCons : {A : Set} -> (l : List A) -> (l Data.List.++ [] ≡ l)
rightCons [] = refl
rightCons (x ∷ l) rewrite rightCons l = refl

rSubsetStar : (r : RETypes.RE RETypes.NonNull) -> (s : List Char) -> RETypes.REMatch s r -> RETypes.REMatch s (r RETypes.*)
rSubsetStar RETypes.∅ [] ()
rSubsetStar (RETypes.Lit x) [] ()
rSubsetStar (r RETypes.+ r₁) [] match = {!!}
rSubsetStar (r RETypes.· r₁) [] match = {!!} --TODO why is this case possible?
rSubsetStar r (x ∷ s) match = RETypes.StarMatch match RETypes.EmptyStarMatch --RETypes.StarMatch {!!} RETypes.EmptyStarMatch 

unpackStarSemi : {n : ℕ} -> {r : RETypes.RE RETypes.NonNull} -> (cmap : Char -> Fin.Fin n) -> (v : Parikh n) -> InSemiLin v (reSemiLin cmap (r RETypes.*)) -> LinComb v (concatLinSets (reSemiLin cmap r) )
unpackStarSemi cmap v (InHead .v ._ .[] lcomb) = lcomb
unpackStarSemi cmap v (InTail .v ._ .[] ()) 

reParikhCorrect : 
  {n : ℕ} 
  -> {null? : RETypes.Null?} 
  -> (cmap : Char -> Fin.Fin n) 
  -> (r : RETypes.RE null?) 
  -> (w : List Char ) 
  -> RETypes.REMatch w r
  -> (wordPar : Parikh n)
  -> (wordParikh cmap w ≡ wordPar)
  -> (langParikh : SemiLinSet n)
  -> (langParikh ≡ reSemiLin cmap r )
  -> (InSemiLin wordPar langParikh ) 
reParikhCorrect cmap .RETypes.ε .[] RETypes.EmptyMatch .v0 refl .((v0 , 0 , []) ∷ []) refl = InHead v0 (v0 , zero , []) [] ([] , refl) 
reParikhCorrect cmap .(RETypes.Lit c) .(c ∷ []) (RETypes.LitMatch c) .(basis (cmap c) +v v0) refl .((basis (cmap c) , 0 , []) ∷ []) refl = 
  InHead (basis (cmap c) +v v0) (basis (cmap c) , zero , []) [] (subst (λ x → LinComb x (basis (cmap c) , zero , [])) (sym v0identRight) (v0 , (v0apply (basis (cmap c)) []))) 
reParikhCorrect cmap (r1 RETypes.+ .r2) w (RETypes.LeftPlusMatch r2 match) wordPar wpf langParikh lpf =
  let
    leftParikh = reSemiLin cmap r1
    leftInSemi = reParikhCorrect cmap r1 w match wordPar wpf leftParikh refl
    --Idea: show that langParikh is leftParikh ++ rightParikh
    --And that this means that it must be in the concatentation
    extendToConcat : InSemiLin wordPar ((reSemiLin cmap r1 ) Data.List.++ (reSemiLin cmap r2))
    extendToConcat = slConcatRight wordPar (reSemiLin cmap r1) leftInSemi (reSemiLin cmap r2)
  in subst (λ x → InSemiLin wordPar x) (sym lpf) extendToConcat
reParikhCorrect cmap (.r1 RETypes.+ r2) w (RETypes.RightPlusMatch r1 match) wordPar wpf langParikh lpf = let
    rightParikh = reSemiLin cmap r2
    rightInSemi = reParikhCorrect cmap r2 w match wordPar wpf rightParikh refl
    --Idea: show that langParikh is leftParikh ++ rightParikh
    --And that this means that it must be in the concatentation
    extendToConcat : InSemiLin wordPar ((reSemiLin cmap r1 ) Data.List.++ (reSemiLin cmap r2))
    extendToConcat = slConcatLeft wordPar (reSemiLin cmap r2) rightInSemi (reSemiLin cmap r1)
  in subst (λ x → InSemiLin wordPar x) (sym lpf) extendToConcat
reParikhCorrect cmap (r1 RETypes.· r2) s3 (RETypes.ConcatMatch {s1 = s1} {s2 = s2} {spf = spf} match1 match2) .(wordParikh cmap s3) refl ._ refl rewrite (sym spf) |  (wordParikhPlus cmap s1 s2) =
 let
    leftParikh = reSemiLin cmap r1
    leftInSemi : InSemiLin (wordParikh cmap s1) leftParikh
    leftInSemi = reParikhCorrect cmap r1 s1 match1 (wordParikh cmap s1) refl (reSemiLin cmap r1) refl 

    rightParikh = reSemiLin cmap r2
    rightInSemi : InSemiLin (wordParikh cmap s2) rightParikh
    rightInSemi = reParikhCorrect cmap r2 s2 match2 (wordParikh cmap s2) refl (reSemiLin cmap r2) refl

    wordParikhIsPlus : (wordParikh cmap s1) +v (wordParikh cmap s2) ≡ (wordParikh cmap (s1 Data.List.++ s2 )) 
    wordParikhIsPlus = sym (wordParikhPlus cmap s1 s2)

  in sumPreserved (wordParikh cmap s1) (wordParikh cmap s2) leftParikh rightParikh leftInSemi rightInSemi
reParikhCorrect cmap (r RETypes.*) [] RETypes.EmptyStarMatch .v0 refl .(concatLinSets (reSemiLin cmap r) ∷ []) refl with (reSemiLin cmap r) 
reParikhCorrect cmap (r RETypes.*) [] RETypes.EmptyStarMatch .v0 refl .(concatLinSets (reSemiLin cmap r) ∷ []) refl | []  = InHead v0 (concatLinSets []) [] (v0 , refl) 
reParikhCorrect cmap (r RETypes.*) [] RETypes.EmptyStarMatch .v0 refl .(concatLinSets ((xb , xm , xv ) ∷ rsl) ∷ []) refl | (xb , xm , xv ) ∷ rsl =
 InHead v0 (concatLinSets ((xb , xm , xv) ∷ rsl)) [] (v0 , 
    (begin 
      (0 ·ₛ xb) +v
        applyLinComb v0 (xm + proj₁ (proj₂ (concatLinSets rsl)))
        (xv Data.Vec.++ proj₂ (proj₂ (concatLinSets rsl))) v0 
    ≡⟨ cong (λ x → (0 ·ₛ xb) +v x) (v0apply v0 (xv Data.Vec.++ proj₂ (proj₂ (concatLinSets rsl)))) ⟩ 
    (0 ·ₛ xb) +v v0 
    ≡⟨ cong (λ x → x +v v0) (scalar0ident xb) ⟩ 
    v0 +v v0 
    ≡⟨ v0identLeft ⟩ 
    (v0 ∎)))
reParikhCorrect cmap (r RETypes.*) .(c1 ∷ s1t Data.List.++ s2) (RETypes.StarMatch {c1} {s1t} {s2} {.((c1 ∷ s1t) Data.List.++ s2)} {refl} {.r} match match₁) .(wordParikh cmap ((c1 ∷ s1t) Data.List.++ s2)) refl .(concatLinSets (reSemiLin cmap r) ∷ []) refl rewrite wordParikhPlus cmap (c1 ∷ s1t) s2  = 
  InHead ((basis (cmap c1) +v wordParikh cmap s1t) +v wordParikh cmap s2) (concatLinSets (reSemiLin cmap r)) [] 
  (sumEqualVecs (concatLinSets (reSemiLin cmap r)) (concatZeroBase (reSemiLin cmap r)) (basis (cmap c1) +v wordParikh cmap s1t) (wordParikh cmap s2) 
    (unpackStarSemi cmap (basis (cmap c1) +v wordParikh cmap s1t) 
      (reParikhCorrect cmap (r RETypes.*) (c1 ∷ s1t) (rSubsetStar r (c1 ∷ s1t) match) (basis (cmap c1) +v wordParikh cmap s1t) refl (concatLinSets (reSemiLin cmap r) ∷ []) refl)) 
    (unpackStarSemi cmap (wordParikh cmap s2) 
      (reParikhCorrect cmap (r RETypes.*) s2 match₁ (wordParikh cmap s2) refl (concatLinSets (reSemiLin cmap r) ∷ []) refl)))

{-
  let
    firstStarMatch : RETypes.REMatch (c1 ∷ s1t) (r RETypes.*)
    firstStarMatch = rSubsetStar r (c1 ∷ s1t) match
    --subPar = reSemiLin cmap r
    firstMatchPar = wordParikh cmap (c1 ∷ s1t)
    inSubPar : InSemiLin firstMatchPar (concatLinSets (reSemiLin cmap r) ∷ [])
    inSubPar = reParikhCorrect cmap (r RETypes.*) (c1 ∷ s1t) firstStarMatch firstMatchPar refl (concatLinSets (reSemiLin cmap r) ∷ []) refl

    secondMatchPar = wordParikh cmap s2
    inSubPar2 : InSemiLin secondMatchPar (concatLinSets (reSemiLin cmap r) ∷ [])
    inSubPar2 = reParikhCorrect cmap (r RETypes.*) s2 match₁ secondMatchPar refl (concatLinSets (reSemiLin cmap r) ∷ []) refl

    --subPar and langParikh should be paralell, 
    --each lin set in langParikh is just a constant multiplied by
    --the corresponding one in subPar
    --This function iterates to find the corresponding pair

    --Idea: show that s1's parikh is in langParikh. Then, we know s2's parikh is in langParikh, so we show their sum is in langParikh
    --newSemiMatch : InSemiLin firstMatchPar langParikh
    --newSemiMatch = {!!} --findConstMultMatch firstMatchPar subPar langParikh lpf inSubPar
    
  in {!!} -}

decomposeLin
  :  {n : ℕ} 
  -> (v : Parikh n) 
  -> (l1 l2 l3 : LinSet n) 
  -> (l3 ≡ l1 +l l2 ) 
  -> LinComb v l3 
  -> ∃ λ v1 → ∃ λ v2 -> (v1 +v v2 ≡ v) × (LinComb v1 l1) × (LinComb v2 l2 )
decomposeLin .(applyLinComb (b1 +v b2) (m1 + m2) (vecs1 Data.Vec.++ vecs2) coeffs) (b1 , m1 , vecs1) (b2 , m2 , vecs2) .(b1 +v b2 , m1 + m2 , vecs1 Data.Vec.++ vecs2) refl (coeffs , refl) with Data.Vec.splitAt m1 coeffs 
decomposeLin .(applyLinComb (b1 +v b2) (m1 + m2) (vecs1 Data.Vec.++ vecs2) (coeffs1 Data.Vec.++ coeffs2)) (b1 , m1 , vecs1) (b2 , m2 , vecs2) .(b1 +v b2 , m1 + m2 , vecs1 Data.Vec.++ vecs2) refl (.(coeffs1 Data.Vec.++ coeffs2) , refl) | coeffs1 , coeffs2 , refl rewrite combSplit b1 b2 m1 m2 vecs1 vecs2 coeffs1 coeffs2 
  = applyLinComb b1 m1 vecs1 coeffs1 , (applyLinComb b2 m2 vecs2 coeffs2 , (refl , ((coeffs1 , refl) , (coeffs2 , refl))))

decomposeSum 
  :  {n : ℕ} 
  -> (v : Parikh n) 
  -> (s1 s2 s3 : SemiLinSet n) 
  -> (s3 ≡ s1 +s s2 ) 
  -> InSemiLin v s3 
  -> ∃ λ v1 → ∃ λ v2 -> (v1 +v v2 ≡ v) × (InSemiLin v1 s1) × (InSemiLin v2 s2 )
decomposeSum v s1 s2 ._ refl inSemi = {!!}



--Useful function for splitting semi-linear sets
--Used for union below
inSemiConcat : 
  {n : ℕ} 
  -> (v : Parikh n) 
  -> (sl1 : SemiLinSet n) 
  -> (sl2 : SemiLinSet n) 
  -> (sl3 : SemiLinSet n)
  -> (sl1 Data.List.++ sl2) ≡ sl3
  ->  InSemiLin v sl3 
  -> (InSemiLin v sl1) ⊎ (InSemiLin v sl2)
inSemiConcat v [] sl2 sl3 spf inSemi = 
  let
    eqPf : sl2 ≡ sl3
    eqPf = spf
  in inj₂ (subst (InSemiLin v) (sym eqPf) inSemi)
inSemiConcat v (x ∷ sl1) sl2 .(sh ∷ st) spf (InHead .v sh st comb) = 
  let
    eqPf : x ≡ sh
    eqPf = listHeadEq spf
    newComb : LinComb v x
    newComb = subst (LinComb v) (sym eqPf) comb
  in inj₁ (InHead v x sl1 newComb)
inSemiConcat v (x ∷ sl1) sl2 .(sh ∷ st) spf (InTail .v sh st inSemi) with inSemiConcat v sl1 sl2 st (listTailEq spf) inSemi 
... | inj₁ inSl1 = inj₁ (InTail v x sl1 inSl1)
... | inj₂ inSl2 = inj₂ inSl2

reParikhComplete : {n : ℕ} -> {null? : RETypes.Null?}
  -> (cmap : Char -> Fin.Fin n)
--  -> (imap : Fin.Fin n -> Char)
--  -> (invPf1 : (x : Char ) -> imap (cmap x) ≡ x)
--  -> (invPf2 : (x : Fin.Fin n ) -> cmap (imap x) ≡ x )
  -> (r : RETypes.RE null?)
  -> (v : Parikh n )
  -> (langParikh : SemiLinSet n)
  -> langParikh ≡ (reSemiLin cmap r )
  -> (InSemiLin v langParikh )
  -> ∃ (λ w -> (v ≡ wordParikh cmap w) × (RETypes.REMatch w r) ) 
reParikhComplete cmap RETypes.ε .v0 .((v0 , 0 , []) ∷ []) refl (InHead .v0 .(v0 , 0 , []) .[] (combConsts , refl)) = [] , refl , RETypes.EmptyMatch
reParikhComplete cmap RETypes.ε v .((v0 , 0 , []) ∷ []) refl (InTail .v .(v0 , 0 , []) .[] ())

--reParikhComplete cmap  RETypes.ε v .(sh ∷ st) lpf (InTail .v sh st inSemi) = {!!}
reParikhComplete cmap  RETypes.∅ v [] lpf ()
reParikhComplete cmap  RETypes.∅ v (h ∷ t) () inSemi 
reParikhComplete cmap (RETypes.Lit x) langParikh [] inSemi ()
reParikhComplete cmap (RETypes.Lit x) .(basis (cmap x)) .((basis (cmap x) , 0 , []) ∷ []) refl (InHead .(basis (cmap x)) .(basis (cmap x) , 0 , []) .[] (consts , refl)) = (x ∷ []) , (sym v0identRight , RETypes.LitMatch x)
reParikhComplete cmap (RETypes.Lit x) v .((basis (cmap x) , 0 , []) ∷ []) refl (InTail .v .(basis (cmap x) , 0 , []) .[] ())
--reParikhComplete cmap (RETypes.Lit x) v .((basis (cmap x) , 0 , []) ∷ []) refl (InTail .v .(basis (cmap x) , 0 , []) .[] ())
reParikhComplete {null? = null?} cmap  (r1 RETypes.+ r2) v langParikh lpf inSemi with inSemiConcat v (reSemiLin cmap r1) (reSemiLin cmap r2) langParikh (sym (trans lpf refl)) inSemi
... | inj₁ in1 =  
  let
    (subw , subPf , subMatch) = reParikhComplete cmap  r1 v (reSemiLin cmap r1) refl in1
  in subw , (subPf , (RETypes.LeftPlusMatch r2 subMatch))
... | inj₂ in2 =  
  let
    (subw , subPf , subMatch) = reParikhComplete cmap  r2 v (reSemiLin cmap r2) refl in2
  in subw , (subPf , (RETypes.RightPlusMatch r1 subMatch))
reParikhComplete cmap (r1 RETypes.· r2) v ._ refl inSemi = 
  let
    
    subSemi1 = reSemiLin cmap r1
    subSemi2 = reSemiLin cmap r2
    langParikh = subSemi1 +s subSemi2

    subInSemiPair : InSemiLin v subSemi1 × InSemiLin v subSemi2
    subInSemiPair = {!!} --TODO do the math for this case
    (inLeftSemi , inRightSemi) = subInSemiPair
    (leftW , leftPf , leftMatch) = reParikhComplete cmap  r1 v subSemi1 refl {!!}
    (rightW , rightPf , rightMatch) = reParikhComplete cmap  r2 v subSemi2 refl {!!}
    wordConcat : (wordParikh cmap leftW) +v (wordParikh cmap rightW) ≡ wordParikh cmap (leftW Data.List.++ rightW)
    wordConcat = sym (wordParikhPlus cmap leftW rightW)
  in leftW Data.List.++ rightW ,
     {!!} , {!!} --(trans {!!} {!!} , (RETypes.ConcatMatch leftMatch rightMatch))

reParikhComplete cmap (r RETypes.*) v .(concatLinSets (reSemiLin cmap r) ∷ []) refl (InHead .v .(concatLinSets (reSemiLin cmap r)) .[] (combVecs , combPf)) 
  with v0 VecNatEq.≟ v
reParikhComplete cmap (r RETypes.*) .[] .(concatLinSets (reSemiLin cmap r) ∷ []) refl (InHead .[] .(concatLinSets (reSemiLin cmap r)) .[] (combVecs , combPf)) | yes Equality.[]-cong = 
  [] , (refl , RETypes.EmptyStarMatch)
reParikhComplete cmap (r RETypes.*) v .(concatLinSets (reSemiLin cmap r) ∷ []) refl (InHead .v .(concatLinSets (reSemiLin cmap r)) .[] (combVecs , combPf)) | no ¬p = {!!}
reParikhComplete cmap (r RETypes.*) v .(concatLinSets (reSemiLin cmap r) ∷ []) refl (InTail .v .(concatLinSets (reSemiLin cmap r)) .[] ())

--Create module
--Instantiate module, with setoid argument
--Rewrite, under the hood, pattern matches that proof is refl
--Won't always work in functions inside the proofs, get unification problems with functions

--If use fns, do a with which has 3 variables
--LHS, RHS, and pf that LHS == RHS, pattern match on proof, see that it's refl
--Unifies left and right
