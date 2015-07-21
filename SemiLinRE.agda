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


rightCons : {A : Set} -> (l : List A) -> (l Data.List.++ [] ≡ l)
rightCons [] = refl
rightCons (x ∷ l) rewrite rightCons l = refl

rSubsetStar : (r : RETypes.RE RETypes.NonNull) -> (s : List Char) -> RETypes.REMatch s r -> RETypes.REMatch s (r RETypes.*)
rSubsetStar RETypes.∅ [] ()
rSubsetStar (RETypes.Lit x) [] ()
rSubsetStar (r RETypes.+ r₁) [] (RETypes.LeftPlusMatch .r₁ match) = RETypes.EmptyStarMatch
rSubsetStar (r RETypes.+ r₁) [] (RETypes.RightPlusMatch .r match) = RETypes.EmptyStarMatch
rSubsetStar (r RETypes.· r₁) [] match = RETypes.EmptyStarMatch 
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

--If a vector is in the union of two semi-linear sets, it must be inside on of them
decomposeConcat 
  :  {n : ℕ} 
  -> (v : Parikh n) 
  -> (s1 s2 s3 : SemiLinSet n) 
  -> (s3 ≡ s1 Data.List.++ s2 ) 
  -> InSemiLin v s3 
  -> InSemiLin v s1 ⊎ InSemiLin v s2
decomposeConcat v [] s2 .s2 refl inSemi = inj₂ inSemi
decomposeConcat v (x ∷ s1) s2 .(x ∷ s1 Data.List.++ s2) refl (InHead .v .x .(s1 Data.List.++ s2) x₁) = inj₁ (InHead v x s1 x₁)
decomposeConcat v (x ∷ s1) s2 .(x ∷ s1 Data.List.++ s2) refl (InTail .v .x .(s1 Data.List.++ s2) inSemi) with decomposeConcat v s1 s2 _ refl inSemi
decomposeConcat v (x₁ ∷ s1) s2 .(x₁ ∷ s1 Data.List.++ s2) refl (InTail .v .x₁ .(s1 Data.List.++ s2) inSemi) | inj₁ x = inj₁ (InTail v x₁ s1 x)
decomposeConcat v (x ∷ s1) s2 .(x ∷ s1 Data.List.++ s2) refl (InTail .v .x .(s1 Data.List.++ s2) inSemi) | inj₂ y = inj₂ y

concatEq : {n : ℕ} -> (l : LinSet n) -> (s : SemiLinSet n) -> (l ∷ []) +s s ≡ (Data.List.map (_+l_ l) s)
concatEq l [] = refl
concatEq l (x ∷ s) rewrite concatEq l s | listIdentity (l ∷ [])  = refl 


decomposeSum 
  :  {n : ℕ} 
  -> (v : Parikh n) 
  -> (s1 s2 s3 : SemiLinSet n) 
  -> (s3 ≡ s1 +s s2 ) 
  -> InSemiLin v s3 
  -> ∃ λ (v1 : Parikh n) → ∃ λ (v2 : Parikh n) -> (v1 +v v2 ≡ v) × (InSemiLin v1 s1) × (InSemiLin v2 s2 )
decomposeSum v [] [] .[] refl ()
decomposeSum v [] (x ∷ s2) .[] refl ()
decomposeSum v (x ∷ s1) [] .(Data.List.foldr Data.List._++_ [] (Data.List.map (λ l1 → []) s1)) refl ()
decomposeSum v ((b1 , m1 , vecs1) ∷ s1) ((b2 , m2 , vecs2) ∷ s2) ._ refl (InHead .v .(b1 +v b2 , m1 + m2 , vecs1 Data.Vec.++ vecs2) ._ lcomb) =
  let
    (v1 , v2 , plusPf , comb1 , comb2 ) = decomposeLin v (b1 , m1 , vecs1) (b2 , m2 , vecs2) (b1 +v b2 , m1 + m2 , vecs1 Data.Vec.++ vecs2) refl lcomb
  in v1 , v2 , plusPf , InHead v1 (b1 , m1 , vecs1) s1 comb1 , InHead v2 (b2 , m2 , vecs2) s2 comb2
decomposeSum v ((b1 , m1 , vecs1) ∷ s1) ((b2 , m2 , vecs2) ∷ s2) ._ refl (InTail .v .(b1 +v b2 , m1 + m2 , vecs1 Data.Vec.++ vecs2) ._ inSemi) with decomposeConcat v (Data.List.map (_+l_ (b1 , m1 , vecs1)) s2) (Data.List.foldr Data.List._++_ []
                                                                                                                                                                                                                     (Data.List.map
                                                                                                                                                                                                                      (λ z → z +l (b2 , m2 , vecs2) ∷ Data.List.map (_+l_ z) s2) s1)) (Data.List.map (_+l_ (b1 , m1 , vecs1)) s2 Data.List.++
                                                                                                                                                                                                                                                                                         Data.List.foldr Data.List._++_ []
                                                                                                                                                                                                                                                                                         (Data.List.map
                                                                                                                                                                                                                                                                                          (λ z → z +l (b2 , m2 , vecs2) ∷ Data.List.map (_+l_ z) s2) s1)) refl inSemi
decomposeSum v ((b1 , m1 , vecs1) ∷ s1) ((b2 , m2 , vecs2) ∷ s2) .((b1 , m1 , vecs1) +l (b2 , m2 , vecs2) ∷ Data.List.map (_+l_ (b1 , m1 , vecs1)) s2 Data.List.++ Data.List.foldr Data.List._++_ [] (Data.List.map _ s1)) refl (InTail .v .(b1 +v b2 , m1 + m2 , vecs1 Data.Vec.++ vecs2) .(Data.List.map (_+l_ (b1 , m1 , vecs1)) s2 Data.List.++ Data.List.foldr Data.List._++_ [] (Data.List.map _ s1)) inSemi) | inj₁ inSub = 
  let
    subCall1 = decomposeSum v ((b1 , m1 , vecs1) ∷ []) s2 _ refl (subst (λ x → InSemiLin v x) (sym (concatEq (b1 , m1 , vecs1) s2)) inSub)
    v1 , v2 , pf , xIn , yIn = subCall1
  in v1 , (v2 , (pf , (slCons v1 s1 (b1 , m1 , vecs1) xIn , slExtend v2 s2 yIn (b2 , m2 , vecs2))))
decomposeSum v ((b1 , m1 , vecs1) ∷ s1) ((b2 , m2 , vecs2) ∷ s2) .((b1 , m1 , vecs1) +l (b2 , m2 , vecs2) ∷ Data.List.map (_+l_ (b1 , m1 , vecs1)) s2 Data.List.++ Data.List.foldr Data.List._++_ [] (Data.List.map _ s1)) refl (InTail .v .(b1 +v b2 , m1 + m2 , vecs1 Data.Vec.++ vecs2) .(Data.List.map (_+l_ (b1 , m1 , vecs1)) s2 Data.List.++ Data.List.foldr Data.List._++_ [] (Data.List.map _ s1)) inSemi) | inj₂ inSub = 
 let 
   subCall1 = decomposeSum v s1 ((b2 , m2 , vecs2) ∷ s2) _ refl inSub 
   v1 , v2 , pf , xIn , yIn = subCall1
 in v1 , v2 , pf , slExtend v1 s1 xIn (b1 , m1 , vecs1) , yIn
{- 
  let
    test : InSemiLin v
             (Data.List.map (_+l_ (b1 , m1 , vecs1)) s2 Data.List.++
              Data.List.foldr Data.List._++_ []
              (Data.List.map
               (λ z → z +l (b2 , m2 , vecs2) ∷ Data.List.map (_+l_ z) s2) s1))
    test = inSemi
  in {!!} -}
{-
test : InSemiLin v
             (Data.List.map (_+l_ (b1 , m1 , vecs1)) s2 Data.List.++
              Data.List.foldr Data.List._++_ []
              (Data.List.map
               (λ z → z +l (b2 , m2 , vecs2) ∷ Data.List.map (_+l_ z) s2) s1))
    test = inSemi
-}


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
reParikhComplete cmap (r1 RETypes.· r2) v ._ refl inSemi with decomposeSum v (reSemiLin cmap r1) (reSemiLin cmap r2) (reSemiLin cmap r1 +s reSemiLin cmap r2) refl inSemi | reParikhComplete cmap r1 (proj₁ (decomposeSum v (reSemiLin cmap r1) (reSemiLin cmap r2)
                                                                                                                                                                                                               (reSemiLin cmap r1 +s reSemiLin cmap r2) refl inSemi)) (reSemiLin cmap r1) refl (proj₁ (proj₂ (proj₂ (proj₂ (decomposeSum v (reSemiLin cmap r1) (reSemiLin cmap r2)
                                                                                                                                                                                                                                                                                                                              (reSemiLin cmap r1 +s reSemiLin cmap r2) refl inSemi))))) | reParikhComplete cmap r2 (proj₁ (proj₂ (decomposeSum v (reSemiLin cmap r1) (reSemiLin cmap r2)
                                                                                                                                                                                                                                                                                                                                                                                                                                    (reSemiLin cmap r1 +s reSemiLin cmap r2) refl inSemi))) (reSemiLin cmap r2) refl (proj₂ (proj₂ (proj₂ (proj₂ (decomposeSum v (reSemiLin cmap r1) (reSemiLin cmap r2)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (reSemiLin cmap r1 +s reSemiLin cmap r2) refl inSemi))))) 
reParikhComplete cmap (r1 RETypes.· r2) .(wordParikh cmap w1 +v wordParikh cmap w2) .(Data.List.foldr Data.List._++_ [] (Data.List.map _ (reSemiLin cmap r1))) refl inSemi | .(wordParikh cmap w1) , .(wordParikh cmap w2) , refl , inSemi1 , inSemi2 | w1 , refl , match1 | w2 , refl , match2 = (w1 Data.List.++ w2) , ((sym (wordParikhPlus cmap w1 w2)) , (RETypes.ConcatMatch match1 match2))
{-  let 
    subLeft = reParikhComplete cmap r1 v1 (reSemiLin cmap r1) refl inSemi1
    (w1 , pf1 , match1 ) = subLeft 
    subRight = reParikhComplete cmap r2 v2 (reSemiLin cmap r2) refl inSemi2
    (w2 , pf2 , match2 ) = subRight
    wpPlus = sym (wordParikhPlus cmap w1 w2)
  in w1 Data.List.++ w2 , (sym {!!} , RETypes.ConcatMatch match1 match2) -}
{- 
  let
    
    subSemi1 = reSemiLin cmap r1
    subSemi2 = reSemiLin cmap r2
    langParikh = subSemi1 +s subSemi2

    --subInSemis : InSemiLin v subSemi1 × InSemiLin v subSemi2
    deomp = decomposeSum v subSemi1 subSemi2 langParikh refl inSemi --TODO do the math for this case
    (refl , inLeftSemi , inRightSemi) = subInSemiPair
    (leftW , leftPf , leftMatch) = reParikhComplete cmap  r1 v subSemi1 refl {!!}
    (rightW , rightPf , rightMatch) = reParikhComplete cmap  r2 v subSemi2 refl {!!}
    wordConcat : (wordParikh cmap leftW) +v (wordParikh cmap rightW) ≡ wordParikh cmap (leftW Data.List.++ rightW)
    wordConcat = sym (wordParikhPlus cmap leftW rightW)
  in leftW Data.List.++ rightW ,
     {!!} , {!!} --(trans {!!} {!!} , (RETypes.ConcatMatch leftMatch rightMatch))
-}

reParikhComplete cmap (r RETypes.*) v .(concatLinSets (reSemiLin cmap r) ∷ []) refl (InHead .v .(concatLinSets (reSemiLin cmap r)) .[] (combVecs , combPf)) 
  with v0 VecNatEq.≟ v
reParikhComplete cmap (r RETypes.*) .[] .(concatLinSets (reSemiLin cmap r) ∷ []) refl (InHead .[] .(concatLinSets (reSemiLin cmap r)) .[] (combVecs , combPf)) | yes Equality.[]-cong = 
  [] , (refl , RETypes.EmptyStarMatch)
reParikhComplete cmap (r RETypes.*) .(applyLinComb (proj₁ (concatLinSets (reSemiLin cmap r))) (proj₁ (proj₂ (concatLinSets (reSemiLin cmap r)))) (proj₂ (proj₂ (concatLinSets (reSemiLin cmap r)))) combVecs) .(concatLinSets (reSemiLin cmap r) ∷ []) refl (InHead .(applyLinComb (proj₁ (concatLinSets (reSemiLin cmap r))) (proj₁ (proj₂ (concatLinSets (reSemiLin cmap r)))) (proj₂ (proj₂ (concatLinSets (reSemiLin cmap r)))) combVecs) .(concatLinSets (reSemiLin cmap r)) .[] (combVecs , refl)) | no ¬p rewrite concatZeroBase (reSemiLin cmap r) =
  let
    v = (applyLinComb (proj₁ (concatLinSets (reSemiLin cmap r))) (proj₁ (proj₂ (concatLinSets (reSemiLin cmap r)))) (proj₂ (proj₂ (concatLinSets (reSemiLin cmap r)))) combVecs)
    langParikh = (concatLinSets (reSemiLin cmap r)) ∷ []
    ourSplit : ∃ λ witnessWord -> ∃ λ v2 -> (RETypes.REMatch witnessWord r × InSemiLin v2 langParikh × wordParikh cmap witnessWord +v v2 ≡ v ) 
    ourSplit = {!!}
    witnessWord , v2 , witnessMatch , subInSemi , vpf  = ourSplit
    subCall = reParikhComplete cmap (r RETypes.*) v2 langParikh refl subInSemi
    subWord , subPf , subMatch = subCall
  in (witnessWord Data.List.++ subWord) , sym {!!} , (RETypes.StarMatch witnessMatch subMatch)
reParikhComplete cmap (r RETypes.*) v .(concatLinSets (reSemiLin cmap r) ∷ []) refl (InTail .v .(concatLinSets (reSemiLin cmap r)) .[] ())

--Create module
--Instantiate module, with setoid argument
--Rewrite, under the hood, pattern matches that proof is refl
--Won't always work in functions inside the proofs, get unification problems with functions

--If use fns, do a with which has 3 variables
--LHS, RHS, and pf that LHS == RHS, pattern match on proof, see that it's refl
--Unifies left and right
