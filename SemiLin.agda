module SemiLin where

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




--The Parikh vector for a word is the count of occurrences of
--each letter of our alphabet in that word.
--We represent this by a function which
--maps each character in a list to a natural number
Parikh : ℕ -> Set
Parikh n = Vec ℕ n

--Scalar multiplication
_·ₛ_ : {n : ℕ} -> ℕ -> Parikh n -> Parikh n
c ·ₛ [] = []
c ·ₛ (x ∷ vt) = (c * x) ∷ (c ·ₛ vt)

--Vector addition
_+v_ : {n : ℕ} -> Parikh n -> Parikh n -> Parikh n
[] +v [] = []
(x ∷ ut) +v (y ∷ vt) = x + y ∷ ut +v vt 

--The zero vector
v0 : {n : ℕ} -> Parikh n
v0 {zero} = []
v0 {suc n} = 0 ∷ v0

--Prove that 0 is a neutral element
v0identLeft : {n : ℕ} -> {v : Parikh n} -> v0 +v v ≡ v
v0identLeft {v = []} = refl
v0identLeft {v = x ∷ v} = 
  let
    subIdent = v0identLeft {v = v}
  in cong (λ t → x ∷ t) subIdent

v0commut : {n : ℕ} -> (u : Parikh n) -> (v : Parikh n) -> (u +v v ≡ v +v u)
v0commut [] [] = refl
v0commut (x ∷ u) (y ∷ v) = 
  let
    natCommut : x + y ≡ y + x
    natCommut = +-comm x y 
    tailSame : u +v v ≡ v +v u
    tailSame = v0commut u v 
  in subst (λ z → (x ∷ u) ≡ (z ∷ v)) natCommut (cong (λ t → x ∷ t) tailSame)

v0identRight : {n : ℕ} -> {v : Parikh n} -> v +v v0 ≡ v
v0identRight {v = v} = trans (v0commut v v0) v0identLeft

--A linear set is defined by an offset vector b
--And a set of m vectors v1 ... vm.
--A vector u is in a linear set if there exists constants c1 ... cm
--such that u = b + c1·v1 + ... + cm·vm 
LinSet : ℕ -> Set
LinSet n = (Parikh n) × (∃ λ (m : ℕ) → Vec (Parikh n) m )

--A type acting as a witness that a vector is in a linear set
LinComb : {n : ℕ} -> Parikh n -> LinSet n -> Set
LinComb {n} initV (base , m , vset)  = 
  ∃ (λ (cs : Vec ℕ m) -> 
    let 
      multFuns : Vec (Parikh n -> Parikh n) m
      multFuns = Data.Vec.map (λ (c : ℕ) → λ (v : Parikh n) → c ·ₛ v) cs
      scaledVecs : Vec (Parikh n) m
      scaledVecs = multFuns ⊛ vset
      comb : Parikh n
      comb = Data.Vec.foldr (\_ -> Parikh n) _+v_ v0 scaledVecs
    in (base +v comb) ≡ initV )

--A semi-linear is a finite union of linear sets
--We represent this using a list
--TODO Vector?
SemiLinSet : ℕ -> Set
SemiLinSet n = List (LinSet n)

--Data type for a witness that an element is in a semiLinear set
--Basically just a proof that there's some element (linear set) of the list containing the vector
data InSemiLin : {n : ℕ} -> (v : Parikh n) -> (sl : SemiLinSet n) -> Set where
  InHead : {n : ℕ} 
    -> (v : Parikh n) 
    -> (sh : LinSet n) 
    -> (st : SemiLinSet n)
    -> LinComb v sh
    -> InSemiLin v (sh ∷ st)
  InTail : {n : ℕ} 
    -> (v : Parikh n) 
    -> (sh : LinSet n) 
    -> (st : SemiLinSet n)
    -> InSemiLin v st
    -> InSemiLin v (sh ∷ st)

slExtend : {n : ℕ} -> (v : Parikh n) -> (sl : SemiLinSet n) -> InSemiLin v sl -> (ls : LinSet n) -> InSemiLin v (ls ∷ sl )
slExtend v sl inTail ls = InTail v ls sl inTail

slConcatLeft : {n : ℕ} -> (v : Parikh n) -> (sl : SemiLinSet n) -> InSemiLin v sl -> (sl2 : SemiLinSet n) -> InSemiLin v (sl2 Data.List.++  sl )
slConcatLeft v sl inTail [] = inTail
slConcatLeft v sl inTail (x ∷ sl2) = InTail v x (sl2 Data.List.++ sl) (slConcatLeft v sl inTail sl2)

slConcatRight : {n : ℕ} -> (v : Parikh n) -> (sl : SemiLinSet n) -> InSemiLin v sl -> (sl2 : SemiLinSet n) -> InSemiLin v (sl Data.List.++  sl2 )
slConcatRight v .(sh ∷ st) (InHead .v sh st x) sl2 = (InHead v sh (st Data.List.++ sl2) x)
slConcatRight v .(sh ∷ st) (InTail .v sh st inTail) sl2 = slExtend v (st Data.List.++ sl2) (slConcatRight v st inTail sl2) sh

--Sum of each vector in a linear set
_+l_ : {n : ℕ} -> LinSet n -> LinSet n -> LinSet n
(base1 , m1 , vecs1 ) +l (base2 , m2 , vecs2 ) = 
  let
    vecs = Data.Vec.concat (Data.Vec.map (λ v1 -> Data.Vec.map (λ v2 -> v1 +v v2  ) vecs1 ) vecs2)
  in base1 +v base2 , m2 * m1 , vecs


--Sum each linear set in the two semi-linear sets
_+s_ : {n : ℕ} -> SemiLinSet n -> SemiLinSet n -> SemiLinSet n
s1 +s s2 = Data.List.concat (Data.List.map (λ l1 -> Data.List.map (λ l2 -> l1 +l l2 )  s2 ) s1 )



--Creates a  vector
--Which has 1 in the specified component, and 0 elsewhere
basis : { n : ℕ} -> ( i : Fin.Fin n ) -> Parikh n
basis Fin.zero  = Data.Vec.[ suc zero ] Data.Vec.++ v0 
basis (Fin.suc f) = 0 ∷ basis f 

--Used in star: given a linear set L, return { cl | l ∈ L, c ∈ ℕ}
--constMultLin : { n : ℕ} -> LinSet n -> LinSet n
--constMultLin (base , m , vecs ) = v0 , suc m , base ∷ vecs

concatLinSets : {n : ℕ } -> SemiLinSet n -> LinSet n
concatLinSets [] = (v0 , 0 , [])
concatLinSets {n} ((base , m ,  linVecs ) ∷ otherLins) = 
  let
    newVecs : Vec (Parikh n) (suc m)
    newVecs = (base ∷ linVecs)
    (_ , m2 , subVecs) = concatLinSets otherLins
  in v0 , ((suc (m) + m2) , newVecs Data.Vec.++ subVecs)

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

--Find the Parikh vector of a given word
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
wordParikhPlus cmap (x ∷ u) v = 
  let
    subSum : wordParikh cmap (u Data.List.++ v) ≡ (wordParikh cmap u) +v (wordParikh cmap v)
    subSum = wordParikhPlus cmap u v
    charBasis : wordParikh cmap Data.List.[ x ] ≡ basis (cmap x)
    charBasis = v0identRight
    listConcat : ((x ∷ u) Data.List.++ v ) ≡ Data.List.[ x ] Data.List.++ ( (u Data.List.++ v) )
    listConcat = {!!}
  in {!!}

--Show that the sum of two vectors is in the sum of semilin sets containing them
sumPreserved : 
  {n : ℕ} 
  -> (u : Parikh n) 
  -> (v : Parikh n)
  -> (uv : Parikh n)
  -> (su : SemiLinSet n) 
  -> (sv : SemiLinSet n)
  -> (suv : SemiLinSet n)
  -> (uv ≡ u +v v)
  -> (suv ≡ su +s sv)
  -> InSemiLin u su
  -> InSemiLin v sv
  -> InSemiLin uv suv
sumPreserved = {!!}

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
    inSum1 = sumPreserved (wordParikh cmap s1) (wordParikh cmap s2) (wordParikh cmap s1 +v wordParikh cmap s2) leftParikh rightParikh (leftParikh +s rightParikh) refl refl leftInSemi rightInSemi 

    inSum2 : InSemiLin wordPar (leftParikh +s rightParikh )
    inSum2 = subst (λ x → InSemiLin x (leftParikh +s rightParikh)) eqChain2 inSum1
  in subst (λ x → InSemiLin wordPar x) semiIsSum inSum2
reParikhCorrect cmap (r RETypes.*) []  (RETypes.EmptyStarMatch) wordPar wpf langParikh lpf with reSemiLin cmap r | langParikh
reParikhCorrect cmap (r RETypes.*) []  (RETypes.EmptyStarMatch) wordPar wpf langParikh lpf | _ | [] = {!!} --TODO show this case impossible
reParikhCorrect cmap (r RETypes.*) []  (RETypes.EmptyStarMatch) wordPar wpf langParikh lpf | [] | _ ∷ _ = {!!} --TODO show this case impossible
... | subParFirst ∷ subParTail | parFirst ∷ parTail  = 
  let
    parIs0a : wordParikh cmap [] ≡ v0
    parIs0a = refl
    parIs0 : wordPar ≡ v0
    parIs0 = trans (sym wpf) parIs0a
    

    newLPF : (parFirst ∷ parTail) ≡ concatLinSets (subParFirst ∷ subParTail) 
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




reParikhComplete : {n : ℕ} -> {null? : RETypes.Null?}
  -> (cmap : Char -> Fin.Fin n)
  -> (r : RETypes.RE null?)
  -> (v : Parikh n )
  -> (langParikh : SemiLinSet n)
  -> langParikh ≡ (reSemiLin cmap r )
  -> (InSemiLin v langParikh )
  -> ∃ (λ w -> (v ≡ wordParikh cmap w) × (RETypes.REMatch w r) ) 
reParikhComplete cmap RETypes.ε v .(sh ∷ st) lpf (InHead .v sh st linComb) =
  let
    emptyPar : (reSemiLin cmap RETypes.ε ) ≡ (v0 , zero , []) ∷ []
    emptyPar = refl
  in {!!}
reParikhComplete cmap RETypes.∅ v .(sh ∷ st) () (InHead .v sh st x)
reParikhComplete cmap (RETypes.Lit x) v .(sh ∷ st) lpf (InHead .v sh st x₁) = {!!}
reParikhComplete cmap (r RETypes.+ r₁) v .(sh ∷ st) lpf (InHead .v sh st x) = {!!}
reParikhComplete cmap (r RETypes.· r₁) v .(sh ∷ st) lpf (InHead .v sh st x) = {!!}
reParikhComplete cmap (r RETypes.*) v .(sh ∷ st) lpf (InHead .v sh st x) = {!!}
reParikhComplete cmap r v .(sh ∷ st) lpf (InTail .v sh st inSemi) = {!!}


