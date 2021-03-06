{-
Joseph Eremondi
Utrecht University Capita Selecta
UU# 4229924
July 22, 2015
-}

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


--Find the Parikh vector of a given word
--Here cmap is the mapping of each character to its position
--in the Parikh vector
wordParikh : {n : ℕ} -> (Char -> Fin.Fin n) -> (w : List Char) -> Parikh n
wordParikh cmap [] = v0
wordParikh cmap (x ∷ w) = (basis (cmap x)) +v (wordParikh cmap w)

--Show that the Parikh of concatenating two words
--Is the sum of their Parikhs
wordParikhPlus : {n : ℕ} 
  -> (cmap : Char -> Fin.Fin n) 
  -> (u : List Char) 
  -> (v : List Char)
  -> wordParikh cmap (u Data.List.++ v) ≡ (wordParikh cmap u) +v (wordParikh cmap v)
wordParikhPlus cmap [] v = sym v0identLeft
wordParikhPlus {n} cmap (x ∷ u) v  = 
  begin
    basis (cmap x) +v wordParikh cmap (u ++l v)
  ≡⟨ cong (λ y → basis (cmap x) +v y) (wordParikhPlus cmap u v) ⟩ 
    basis (cmap x) +v (wordParikh cmap u +v wordParikh cmap v) 
  ≡⟨ sym vAssoc ⟩ 
    ((basis (cmap x) +v wordParikh cmap u) +v wordParikh cmap v ∎)
    where
      _++l_ = Data.List._++_
  


--The algorithm mapping regular expressions to the Parikh set of
--the language matched by the RE
--We prove this correct below
reSemiLin : {n : ℕ} {null? : RETypes.Null?} -> (Char -> Fin.Fin n) -> RETypes.RE null? -> SemiLinSet n 
reSemiLin cmap RETypes.ε = Data.List.[ v0 , 0 , [] ]
reSemiLin cmap RETypes.∅ = []
reSemiLin cmap (RETypes.Lit x) = Data.List.[ basis (cmap x ) , 0 , [] ]
reSemiLin cmap (r1 RETypes.+ r2) = reSemiLin cmap r1 Data.List.++ reSemiLin cmap r2
reSemiLin cmap (r1 RETypes.· r2) = reSemiLin cmap r1 +s reSemiLin cmap r2
reSemiLin cmap (r RETypes.*)  = starSemiLin (reSemiLin cmap r)



{-
Show that s* ⊆ s +v s*
Not implemented due to time restrictions,
but should be possible, given that linStarExtend is implemented
in SemiLin.agda
-}
starExtend 
  :  {n : ℕ}
  -> (v1 v2 : Parikh n )
  -> ( s ss : SemiLinSet n)
  -> ss ≡ starSemiLin s
  -> InSemiLin v1 s
  -> InSemiLin v2 ss
  -> InSemiLin (v1 +v v2) (starSemiLin s)
starExtend v1 v2 s ss spf inS inSS = {!!}

{-
Show that s* ⊇ s +v s*
Not completely implemented due to time restrictions,
but should be possible, given that linStarDecomp is implemented
in SemiLin.agda.

There are also some hard parts, for example, dealing with the proofs
that the returned vectors are non-zero (otherwise, we'd just trivially return v0 and v)
-}
starDecomp
 :  {n : ℕ}
 -> (v : Parikh n)
 -> (s ss : SemiLinSet n)
 -> v ≢ v0
 -> ss ≡ starSemiLin s
 -> InSemiLin v ss
 -> (∃ λ v1 -> ∃ λ v2 -> v1 +v v2 ≡ v × InSemiLin v1 s × InSemiLin v2 ss × v1 ≢ v0  ) 
starDecomp v s ss vpf spf inSemi = {!!}
{-
starDecomp v sh st .(sh ∷ st) .((v0 , 0 , []) ∷ starSum sh st ∷ []) vnz refl refl (InHead .v .(v0 , 0 , []) .(starSum sh st ∷ []) x) with emptyCombZero v x | vnz (emptyCombZero v x)
starDecomp .v0 sh st .(sh ∷ st) .((v0 , zero , []) ∷ [] Data.List.++ starSum sh st ∷ []) vnz refl refl (InHead .v0 .(v0 , zero , []) .(starSum sh st ∷ []) x) | refl | ()
starDecomp v sh [] .(sh ∷ []) .((v0 , 0 , []) ∷ (proj₁ sh , suc (proj₁ (proj₂ sh)) , proj₁ sh ∷ proj₂ (proj₂ sh)) ∷ []) vnz refl refl (InTail .v .(v0 , 0 , []) .((proj₁ sh , suc (proj₁ (proj₂ sh)) , proj₁ sh ∷ proj₂ (proj₂ sh)) ∷ []) (InHead .v .(proj₁ sh , suc (proj₁ (proj₂ sh)) , proj₁ sh ∷ proj₂ (proj₂ sh)) .[] starComb)) with linStarDecomp v sh _ vnz {!!} refl starComb
starDecomp v sh [] .(sh ∷ []) .((v0 , zero , []) ∷ [] Data.List.++ starSum sh [] ∷ []) vnz refl refl (InTail .v .(v0 , zero , []) .(starSum sh [] ∷ []) (InHead .v .(proj₁ sh , suc (proj₁ (proj₂ sh)) , proj₁ sh ∷ proj₂ (proj₂ sh)) .[] starComb)) | inj₁ lComb = v , v0 , v0identRight , InHead v sh [] lComb , InHead v0 (v0 , zero , []) _ (v0 , refl) , vnz
starDecomp v sh [] .(sh ∷ []) .((v0 , zero , []) ∷ [] Data.List.++ starSum sh [] ∷ []) vnz refl refl (InTail .v .(v0 , zero , []) .(starSum sh [] ∷ []) (InHead .v .(proj₁ sh , suc (proj₁ (proj₂ sh)) , proj₁ sh ∷ proj₂ (proj₂ sh)) .[] starComb)) | inj₂ (v1 , v2 , sumPf , comb1 , comb2 , zpf ) = v1 , v2 , sumPf , InHead v1 sh [] comb1 ,  InTail v2 (v0 , zero , []) _ (InHead v2 _ [] comb2) , zpf
starDecomp v sh [] .(sh ∷ []) .((v0 , 0 , []) ∷ (proj₁ sh , suc (proj₁ (proj₂ sh)) , proj₁ sh ∷ proj₂ (proj₂ sh)) ∷ []) vnz refl refl (InTail .v .(v0 , 0 , []) .((proj₁ sh , suc (proj₁ (proj₂ sh)) , proj₁ sh ∷ proj₂ (proj₂ sh)) ∷ []) (InTail .v .(proj₁ sh , suc (proj₁ (proj₂ sh)) , proj₁ sh ∷ proj₂ (proj₂ sh)) .[] ()))
starDecomp v sh (x ∷ st) .(sh ∷ x ∷ st) .((v0 , 0 , []) ∷ (proj₁ x +v proj₁ (starSum sh st) , suc (proj₁ (proj₂ x) + proj₁ (proj₂ (starSum sh st))) , proj₁ x ∷ proj₂ (proj₂ x) Data.Vec.++ proj₂ (proj₂ (starSum sh st))) ∷ []) vnz refl refl (InTail .v .(v0 , 0 , []) .((proj₁ x +v proj₁ (starSum sh st) , suc (proj₁ (proj₂ x) + proj₁ (proj₂ (starSum sh st))) , proj₁ x ∷ proj₂ (proj₂ x) Data.Vec.++ proj₂ (proj₂ (starSum sh st))) ∷ []) inSemi) = {!!} -}




--Stolen from the stdlib
listIdentity : {A : Set} -> (x : List A) -> (x Data.List.++ [] ) ≡ x
listIdentity [] = refl
listIdentity (x ∷ xs) = cong (_∷_ x) (listIdentity xs)


{-
Show that +s is actually the sum of two sets, that is,
if v1 is in S1, and v2 is in S2, then v1 +v v2
is in S1 +s S2
-}
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


--A useful lemma, avoids having to dig into the List monoid instance
rightCons : {A : Set} -> (l : List A) -> (l Data.List.++ [] ≡ l)
rightCons [] = refl
rightCons (x ∷ l) rewrite rightCons l = refl




{-
Show that, if a vector is in the union of two semi-linear sets,
then it must be in one of those sets.
Used in the proof for Union.
Called concat because we represent semi-linear sets as lists,
so union is just concatenating two semi-linear sets
-}
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


{-
Show that if v is in l1 +l l2, then v = v1 +v v2 for some
v1 in l1 and v2 in l2.
This is the other half of the correcness proof of our sum functions, +l and +s
-}
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




{-
Show that our Parikh function is a superset of the actual Parikh image of a Regular Expression.

We do this by showing that, for every word matching an RE, its Parikh vector
is in the Parikh Image of the RE
-}
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
reParikhCorrect cmap (r RETypes.*) [] RETypes.EmptyStarMatch .v0 refl .(starSemiLin (reSemiLin cmap r)) refl = zeroInStar (reSemiLin cmap r) (starSemiLin (reSemiLin cmap r)) refl
reParikhCorrect cmap (r RETypes.*) .(s1 Data.List.++ s2 ) (RETypes.StarMatch {s1 = s1} {s2 = s2} {spf = refl} m1 m2) ._ refl .(starSemiLin (reSemiLin cmap r)) refl rewrite wordParikhPlus cmap s1 s2 = 
  starExtend (wordParikh cmap s1) (wordParikh cmap s2) (reSemiLin cmap r) _ refl (reParikhCorrect cmap r s1 m1 (wordParikh cmap s1) refl (reSemiLin cmap r) refl) (reParikhCorrect cmap (r RETypes.*) s2 m2 (wordParikh cmap s2) refl (starSemiLin (reSemiLin cmap r)) refl) 



{-
Show that if v is in s1 +s s2, then v = v1 +v v2 for some
v1 in s1 and v2 in s2.
This is the other half of the correcness proof of our sum functions, +l and +s
-}
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
Show that the generated Parikh image is a subset of the actual Parikh image.

We do this by showing that, for every vector in the generated Parikh image,
there's some word matched by the RE whose Parikh vector is that vector.
-}
--We have to convince the compiler that this is terminating
--Since I didn't have time to implement the proofs of non-zero vectors
--Which show that we only recurse on strictly smaller vectors in the Star case
{-# TERMINATING #-}
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
reParikhComplete {null? = null?} cmap  (r1 RETypes.+ r2) v langParikh lpf inSemi with decomposeConcat v (reSemiLin cmap r1) (reSemiLin cmap r2) langParikh lpf inSemi
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

reParikhComplete cmap (r RETypes.*) v langParikh lpf inSemi with (reSemiLin cmap r )
reParikhComplete cmap (r RETypes.*) v .((v0 , 0 , []) ∷ []) refl (InHead .v .(v0 , 0 , []) .[] x) | [] = [] , ((sym (proj₂ x)) , RETypes.EmptyStarMatch)
reParikhComplete cmap (r RETypes.*) v .((v0 , 0 , []) ∷ []) refl (InTail .v .(v0 , 0 , []) .[] ()) | []
reParikhComplete cmap (r RETypes.*) v .((v0 , 0 , []) ∷ starSum x rsl ∷ []) refl inSemi | x ∷ rsl = 
  let
    --The first hole is the non-zero proofs that I couldn't work out
    --I'm not totally sure about the second, but I think I just need to apply some associativity to inSemi to get it to fit
    --into the second hole. 
    splitVec = starDecomp v (reSemiLin cmap r) _ {!!} refl {!!}
    v1 , v2 , vpf , inS , inSS , _ = splitVec
    subCall1 = reParikhComplete cmap r v1 _ refl inS
    w1 , wpf1 , match  = subCall1
    subCall2 = reParikhComplete cmap (r RETypes.*) v2 _ refl inSS
    w2 , wpf2 , match2 = subCall2
  in (w1 Data.List.++ w2) , (trans (sym vpf) (sym (wordParikhPlus cmap w1 w2)) , RETypes.StarMatch match match2)

