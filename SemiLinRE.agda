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

row : ∀ {A} -> {m n : ℕ} -> Vec A m -> A -> Vec (A × A) m
row [] ys = []
row (x ∷ xs) y = (x , y) ∷ row xs y

allPairs : ∀ {A} -> {m n : ℕ} -> Vec A m -> Vec A n -> Vec (A × A) (n * m) 
allPairs xarg [] = []
allPairs xarg (y ∷ yarg) = row xarg y Data.Vec.++ allPairs xarg yarg

rowWitness : ∀ {A} -> {m : ℕ} -> (xv : Vec A m) -> (x : A) -> (y : A) -> x ∈ xv -> (x , y ) ∈ row xv y
rowWitness ._ x y here = here
rowWitness ._ x y (there xIn) = there (rowWitness _ x y xIn)
    
pairWitness : ∀ {A} -> {m n : ℕ} -> (xv : Vec A m) -> (yv : Vec A n) -> (x : A) -> (y : A) -> x ∈ xv -> y ∈ yv -> (x , y ) ∈ allPairs xv yv
pairWitness ._ ._ x y here here = here
pairWitness ._ ._ x y (there inx) here = {!!}
--... | here  = {!!}
--... | there rw = ?
pairWitness xv ._ x y inx (there iny) = {!!}

inConcat : {n : ℕ} -> (v : Parikh n) -> (su : SemiLinSet n) -> (sv : SemiLinSet n) -> InSemiLin v (su Data.List.++ sv) -> (InSemiLin v su) ⊎ (InSemiLin v sv)
inConcat v [] sv inSemi = inj₂ inSemi
inConcat v (x ∷ su) sv (InHead .v .x .(su Data.List.++ sv) x₁) = {!!}
inConcat v (x ∷ su) sv (InTail .v .x .(su Data.List.++ sv) inSemi) with inConcat v su sv inSemi
... | inj₁ inU = inj₁ (slExtend v su inU x)
... | inj₂ inV = inj₂ inV

+s-commut : {n : ℕ} -> (v : Parikh n) -> (su : SemiLinSet n) -> (sv : SemiLinSet n) -> InSemiLin v (su +s sv) -> InSemiLin v (sv +s su)
+s-commut v [] [] ()
+s-commut v [] (x ∷ sv) ()
+s-commut v (x ∷ su) [] ()
+s-commut v ((ub , um , uvecs) ∷ su) ((vb , vm , vvecs) ∷ sv) (InHead .v .(ub +v vb , um + vm , uvecs Data.Vec.++ vvecs) ._ (combC , combPf))
  rewrite v+-commut ub vb  =
  let
    (combU , combV , pf ) = Data.Vec.splitAt um combC
    ret = InHead v ((vb +v ub) , ((vm + um) , vvecs Data.Vec.++ uvecs)) _ (combV Data.Vec.++ combU , {!combPf!})
  in ret
+s-commut v ((ub , um , uvecs) ∷ su) ((vbase , vm , vvecs) ∷ sv) (InTail .v .(ub +v vbase , um + vm , uvecs Data.Vec.++ vvecs) ._ inSum) = {!!}
--Show that the sum of two vectors is in the sum of SemiLinear sets containing them
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
sumPreserved u v .(sh ∷ st) .(sh₁ ∷ st₁) (InHead .u sh st x) (InHead .v sh₁ st₁ x₁) = {!!}
sumPreserved u v .(sh ∷ st) .(sh₁ ∷ st₁) (InHead .u sh st x) (InTail .v sh₁ st₁ inv) 
  with {!!} -- inConcat (u +v v) (sh ∷ st) st₁ (sumPreserved u v (sh ∷ st) st₁ (InHead u sh st x) inv )
... | _ = {!!} 
sumPreserved u v .(sh ∷ st) .(sh₁ ∷ st₁) (InTail .u sh st inu) (InHead .v sh₁ st₁ x) = {!!}
sumPreserved u v .(sh ∷ st) .(sh₁ ∷ st₁) (InTail .u sh st inu) (InTail .v sh₁ st₁ inv) = {!!}


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
reParikhCorrect cmap (r1 RETypes.· r2) .s3 (RETypes.ConcatMatch {s1 = s1} {s2 = s2} {s3 = s3} {spf = spf} match1 match2) wordPar wpf langParikh lpf =
 let
    leftParikh = reSemiLin cmap r1
    leftInSemi : InSemiLin (wordParikh cmap s1) leftParikh
    leftInSemi = reParikhCorrect cmap r1 s1 match1 (wordParikh cmap s1) refl (reSemiLin cmap r1) refl 

    rightParikh = reSemiLin cmap r2
    rightInSemi : InSemiLin (wordParikh cmap s2) rightParikh
    rightInSemi = reParikhCorrect cmap r2 s2 match2 (wordParikh cmap s2) refl (reSemiLin cmap r2) refl

    langParikhIsPlus : langParikh ≡ leftParikh +s rightParikh
    langParikhIsPlus = lpf

    wordParikhIsPlus : (wordParikh cmap s1) +v (wordParikh cmap s2) ≡ (wordParikh cmap (s1 Data.List.++ s2 )) 
    wordParikhIsPlus = sym (wordParikhPlus cmap s1 s2)
    eqChain1 : (wordParikh cmap s1) +v (wordParikh cmap s2) ≡ (wordParikh cmap (s3 ))
    eqChain1 = subst (λ x → wordParikh cmap s1 +v wordParikh cmap s2 ≡ wordParikh cmap x) spf wordParikhIsPlus

    eqChain2 : (wordParikh cmap s1) +v (wordParikh cmap s2) ≡ wordPar
    eqChain2 = trans eqChain1 wpf

    semiIsSum : (leftParikh +s rightParikh ) ≡ langParikh
    semiIsSum = sym lpf

    inSum1 : InSemiLin ((wordParikh cmap s1) +v (wordParikh cmap s2) ) (leftParikh +s rightParikh )
    inSum1 = {!!} -- sumPreserved (wordParikh cmap s1) (wordParikh cmap s2) (wordParikh cmap s1 +v wordParikh cmap s2) leftParikh rightParikh (leftParikh +s rightParikh) refl refl leftInSemi rightInSemi 

    inSum2 : InSemiLin wordPar (leftParikh +s rightParikh )
    inSum2 = subst (λ x → InSemiLin x (leftParikh +s rightParikh)) eqChain2 inSum1
  in subst (λ x → InSemiLin wordPar x) semiIsSum inSum2
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
reParikhCorrect cmap (r RETypes.*) w (RETypes.StarMatch {c1} {s1t} {s2} {.w} {spf} {.r} match match₁) .(wordParikh cmap w) refl .(concatLinSets (reSemiLin cmap r) ∷ []) refl = 

  let
    subPar = reSemiLin cmap r
    firstMatchPar = wordParikh cmap (c1 ∷ s1t)
    inSubPar : InSemiLin firstMatchPar subPar
    inSubPar = reParikhCorrect cmap r (c1 ∷ s1t) match firstMatchPar refl subPar refl

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
    
  in {!!}



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

reParikhComplete cmap (r RETypes.*) v .(concatLinSets (reSemiLin cmap r) ∷ []) refl (InHead .v .(concatLinSets (reSemiLin cmap r)) .[] (combVecs , combPf)) = {!!}
reParikhComplete cmap (r RETypes.*) v .(concatLinSets (reSemiLin cmap r) ∷ []) refl (InTail .v .(concatLinSets (reSemiLin cmap r)) .[] ())
