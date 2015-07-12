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


open import Utils

open import Function

import RETypes

open import Data.Sum

open import SemiLin



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
sumPreserved {n} u v .(sh ∷ st) .(sh₁ ∷ st₁) (InHead .u sh st lcu) (InHead .v sh₁ st₁ lcv) =
  let
    su = (sh ∷ st)
    sv = (sh₁ ∷ st₁)
    (ubase , um , uvecs) = sh
    (vbase , vm , vvecs) = sh₁
    comb1 , pf1 = lcu
    comb2 , pf2 = lcv
    concatHead : (su +s sv) ≡ (sh +l sh₁) ∷ Data.List.map (_+l_ sh) st₁ Data.List.++
                                              Data.List.foldr Data.List._++_ []
                                              (Data.List.map (λ z → z +l sh₁ ∷ Data.List.map (_+l_ z) st₁) st) 
    concatHead =  refl
    ourComb : Vec ℕ (um + vm)
    ourComb = comb1 Data.Vec.++ comb2
  in InHead (u +v v) (sh +l sh₁) (Data.List.map (_+l_ sh) st₁ Data.List.++
                                    Data.List.foldr Data.List._++_ []
                                    (Data.List.map (λ z → z +l sh₁ ∷ Data.List.map (_+l_ z) st₁) st)) (ourComb , {!!})

sumPreserved {n} u v .(sh ∷ st) .(sh₁ ∷ st₁) (InHead .u sh st x) (InTail .v sh₁ st₁ vIn) = 
  let
    subCall : InSemiLin (u +v v) ((sh ∷ st) +s st₁)
    subCall = sumPreserved u v (sh ∷ st) st₁ (InHead u sh st x) vIn
    sPlusDef : (sh ∷ st) +s (sh₁ ∷ st₁) ≡ {!!}
    sPlusDef = refl
  in {!!}  
  
sumPreserved u v .(sh ∷ st) .(sh₁ ∷ st₁) (InTail .u sh st uIn) (InTail .v sh₁ st₁ vIn) =
  let 
    subCall : InSemiLin (u +v v) (st +s st₁)
    subCall = sumPreserved u v st st₁ uIn vIn
  in {!!}
sumPreserved u v .(sh ∷ st) sv (InTail .u sh st uIn) vIn = {!!}
{-
--Show that if two vectors are both in a semiLin set, then their sum is in that set
--TODO this is wrong
subPreserved2 :   {n : ℕ} 
  -> (u : Parikh n) 
  -> (v : Parikh n)
  -> (uv : Parikh n)
  -> (sl : SemiLinSet n) 
  -> (uv ≡ u +v v)
  -> InSemiLin u sl
  -> InSemiLin v sl
  -> InSemiLin uv sl
subPreserved2 u v uv sl sumPf uInSemi vInSemi = {!!}
-}


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
reParikhCorrect cmap .RETypes.ε .[] RETypes.EmptyMatch wordPar wpf langParikh lpf = 
  let
    emptyWordPar : wordPar ≡ v0
    emptyWordPar = trans (sym wpf) refl
    emptyLangPf : (( v0 , 0 , [] ) ∷ []) ≡ langParikh
    emptyLangPf = sym lpf
    zeroSelf : v0 +v v0 ≡ v0
    zeroSelf = v0identLeft
    inSemi : InSemiLin wordPar (( v0 , 0 , [] ) ∷ [] )
    inSemi = InHead wordPar (v0 , zero , []) [] (v0 , trans zeroSelf (sym emptyWordPar))
  in subst (λ x → InSemiLin wordPar x) emptyLangPf inSemi
reParikhCorrect cmap .(RETypes.Lit c) .(c ∷ []) (RETypes.LitMatch c) wordPar wpf langParikh lpf =
  let
    basisPf : wordPar ≡ (basis (cmap c))
    basisPf = trans (sym wpf) (trans refl v0identRight)
    basisSemiPf : langParikh ≡ Data.List.[ (basis (cmap c)) , 0 , []  ]
    basisSemiPf = lpf
    inSemi : InSemiLin wordPar (( (basis (cmap c)) , 0 , [] ) ∷ [] )
    inSemi = InHead wordPar (basis (cmap c) , 0 , []) [] (v0 , sym (trans basisPf (sym v0identRight)))
  in subst (λ x → InSemiLin wordPar x) (sym basisSemiPf) inSemi
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
reParikhCorrect cmap (r RETypes.*) []  (RETypes.EmptyStarMatch) wordPar wpf langParikh lpf with reSemiLin cmap r | langParikh
reParikhCorrect cmap (r RETypes.*) []  (RETypes.EmptyStarMatch) wordPar wpf langParikh lpf | _ | [] = {!!} --TODO show this case impossible
reParikhCorrect  cmap (r RETypes.*) []  (RETypes.EmptyStarMatch) wordPar wpf langParikh lpf | [] | _ ∷ _ = {!!} --TODO show this case impossible
... | subParFirst ∷ subParTail | parFirst ∷ parTail  = 
  let
    parIs0a : wordParikh cmap [] ≡ v0
    parIs0a = refl
    parIs0 : wordPar ≡ v0
    parIs0 = trans (sym wpf) parIs0a
    
    m = Data.List.length parTail

    --newLPF : (v0 , suc m ,  parFirst ∷ parTail) ≡ concatLinSets (subParFirst ∷ subParTail) 
    newLPF = {!!} -- trans lpf mapFirst

    pbase , pm , pvecs = subParFirst

    headPf : parFirst ≡ (v0 , suc pm , pbase ∷ pvecs)
    headPf = listHeadEq newLPF

    emptyLinComb : LinComb v0 parFirst
    emptyLinComb = v0 , {!!} --TODO prove that v0 dot anything is v0
   

  in InHead wordPar parFirst parTail (subst (λ x → LinComb x parFirst) (sym parIs0) emptyLinComb)

reParikhCorrect {n} cmap (r RETypes.*) w (RETypes.StarMatch {c1 = c1} {s1t = s1t} {s2 = s2} match match₁) wordPar wpf langParikh lpf =
  let
    subPar = reSemiLin cmap r
    firstMatchPar = wordParikh cmap (c1 ∷ s1t)
    inSubPar : InSemiLin firstMatchPar subPar
    inSubPar = reParikhCorrect cmap r (c1 ∷ s1t) match firstMatchPar refl subPar refl

    secondMatchPar = wordParikh cmap s2
    inSubPar2 : InSemiLin secondMatchPar langParikh
    inSubPar2 = reParikhCorrect cmap (r RETypes.*) s2 match₁ secondMatchPar refl langParikh lpf

    --subPar and langParikh should be paralell, 
    --each lin set in langParikh is just a constant multiplied by
    --the corresponding one in subPar
    --This function iterates to find the corresponding pair

    --Idea: show that s1's parikh is in langParikh. Then, we know s2's parikh is in langParikh, so we show their sum is in langParikh
    newSemiMatch : InSemiLin firstMatchPar langParikh
    newSemiMatch = {!!} --findConstMultMatch firstMatchPar subPar langParikh lpf inSubPar
    
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
reParikhComplete {n} cmap RETypes.ε v .(sh ∷ st) lpf (InHead .v sh st linComb) =
  let
    (sh1 , sh2 , sh3) = sh

    emptyPar : (reSemiLin cmap RETypes.ε ) ≡ (v0 , zero , []) ∷ []
    emptyPar = refl
    emptySh : sh ≡ (v0 , zero , [])
    emptySh = listHeadEq lpf
    ( consts , combPf ) = linComb
    test : {!!} ≡ combPf
    test = {!!}
    combVec = (Data.Vec.foldr (λ _ → Parikh n) (λ {n} → _+v_) v0 (Data.Vec.replicate _·ₛ_ ⊛ proj₁ linComb ⊛ proj₂ (proj₂ sh)))

    sub1 : sh2 ≡ zero
    sub1 = cong (proj₁ ∘ proj₂) emptySh

    emptyVecSub : Vec (Parikh n) sh2
    emptyVecSub = subst (λ x → Vec (Parikh n) x) (sym sub1) []

    subTypesEq : Vec (Parikh n) zero ≡ Vec (Parikh n) sh2
    subTypesEq = cong (λ x → Vec (Parikh n) x) (sym sub1)

    sub2 : (sh2 , sh3) ≡ (zero , [])
    sub2 = cong (proj₂ ) emptySh


    expandComb1 : v0 +v combVec ≡ v
    expandComb1 = subst (λ x → x +v combVec ≡ v) (cong proj₁ emptySh) combPf
    

  in [] , {!!} , RETypes.EmptyMatch
reParikhComplete cmap  RETypes.ε v .(sh ∷ st) lpf (InTail .v sh st inSemi) = {!!}
reParikhComplete cmap  RETypes.∅ v [] lpf ()
reParikhComplete cmap  RETypes.∅ v (h ∷ t) () inSemi 
reParikhComplete 
  cmap 
  (RETypes.Lit x) 
  .(basis (cmap x) +v v0) 
  .((basis (cmap x) , 0 , []) ∷ []) 
  refl 
  (InHead .(basis (cmap x) +v v0) .(basis (cmap x) , 0 , []) .[] (combVecs , refl)) = 
    (x ∷ []) , (refl , RETypes.LitMatch x)
reParikhComplete cmap (RETypes.Lit x) v .((basis (cmap x) , 0 , []) ∷ []) refl (InTail .v .(basis (cmap x) , 0 , []) .[] ())
--  let
--    litParPf : langParikh ≡ ((basis (cmap x)) , (0 , [])) ∷ [] --basis (cmap x)
--    litParPf = lpf
--  in (x ∷ []) , {!!}
reParikhComplete {null? = null?} cmap  (r1 RETypes.+ r2) v langParikh lpf inSemi with inSemiConcat v (reSemiLin cmap r1) (reSemiLin cmap r2) langParikh (sym (trans lpf refl)) inSemi
... | inj₁ in1 =  
  let
    (subw , subPf , subMatch) = reParikhComplete cmap  r1 v (reSemiLin cmap r1) refl in1
  in subw , (subPf , (RETypes.LeftPlusMatch r2 subMatch))
... | inj₂ in2 =  
  let
    (subw , subPf , subMatch) = reParikhComplete cmap  r2 v (reSemiLin cmap r2) refl in2
  in subw , (subPf , (RETypes.RightPlusMatch r1 subMatch))
reParikhComplete cmap  (r1 RETypes.· r2) v langParikh lpf inSemi = 
  let
    subSemi1 = reSemiLin cmap r1
    subSemi2 = reSemiLin cmap r2
    subEq : langParikh ≡ subSemi1 +s subSemi2
    subEq = trans lpf refl
    newInSemi : InSemiLin v (subSemi1 +s subSemi2)
    newInSemi = subst (InSemiLin v) subEq inSemi
    subInSemiPair : InSemiLin v subSemi1 × InSemiLin v subSemi2
    subInSemiPair = {!!} --TODO do the math for this case
    (inLeftSemi , inRightSemi) = subInSemiPair
    (leftW , leftPf , leftMatch) = reParikhComplete cmap  r1 v subSemi1 refl inLeftSemi
    (rightW , rightPf , rightMatch) = reParikhComplete cmap  r2 v subSemi2 refl inRightSemi

    w = leftW Data.List.++ rightW
  
     
    wordConcat = sym (wordParikhPlus cmap leftW rightW)

  in w , (trans {!!} {!!} , (RETypes.ConcatMatch leftMatch rightMatch))
reParikhComplete cmap  (r RETypes.*) v w lpf inSemi = {!!}
