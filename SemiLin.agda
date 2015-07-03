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

open import Data.Sum

import Data.Nat.Properties.Simple




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

vAssoc : {n : ℕ} -> {x : Parikh n} {y : Parikh n} {z : Parikh n}
  -> (x +v y) +v z ≡ x +v (y +v z) 
vAssoc {zero} {[]} {[]} {[]} = refl
vAssoc {suc n} {xh ∷ xt} {yh ∷ yt} {zh ∷ zt} = 
  let
    x = xh ∷ xt
    y = yh ∷ yt
    z = zh ∷ zt
    headSum = (xh + yh) + zh
    tailSum = (xt +v yt) +v zt
    tailRec : (xt +v yt) +v zt ≡ xt +v (yt +v zt)
    tailRec = vAssoc
    topDivide : (x +v y) +v z ≡ ( ((xh + yh ) + zh ) ∷ ((xt +v yt) +v zt))
    topDivide = refl
    normalAddAssoc : (xh + yh) + zh ≡ xh + (yh + zh)
    normalAddAssoc = Data.Nat.Properties.Simple.+-assoc xh yh zh
    tailAssoc : ((xt +v yt) +v zt) ≡ (xt +v (yt +v zt))
    tailAssoc = vAssoc {n} {xt} {yt} {zt}
    subAnswer1 : ((xh + yh) + zh) ∷ ((xt +v yt) +v zt) ≡ ((xh + yh) + zh) ∷ (xt +v (yt +v zt))
    subAnswer1 = cong (\y -> ((xh + yh) + zh) ∷ y) tailAssoc
    subAnswer2 : ((xh + yh) + zh) ∷ ((xt +v yt) +v zt) ≡ (xh + (yh + zh)) ∷ (xt +v (yt +v zt))
    subAnswer2 = subst (λ y -> ((xh + yh) + zh) ∷ ((xt +v yt) +v zt) ≡ y ∷ (xt +v (yt +v zt)) ) normalAddAssoc subAnswer1
    subAnswer3 : (x +v y) +v z ≡ (xh + (yh + zh)) ∷ (xt +v (yt +v zt))
    subAnswer3 = trans topDivide subAnswer2

    rhsSplit : (xh + (yh + zh)) ∷ (xt +v (yt +v zt)) ≡ x +v (y +v z)
    rhsSplit = refl 
     
  in trans subAnswer3 rhsSplit

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
    subSum : wordParikh cmap (u ++l v) ≡ (wordParikh cmap u) +v (wordParikh cmap v)
    subSum = wordParikhPlus cmap u v
    charBasis : wordParikh cmap (x ∷ []) ≡ basis (cmap x)
    charBasis = v0identRight
    concatCons : x ∷ u ≡ (x ∷ [] ) ++l u
    concatCons = refl
    listConcat :  (x ∷ []) Data.List.++ ( (u Data.List.++ v) ) ≡ (x ∷ u) Data.List.++ v 
    listConcat = refl
    uv = u ++l v
    puv = (wordParikh cmap u +v (wordParikh cmap v)) 
    subLetterSum : (wordParikh cmap ((x ∷ []) ++l uv )) 
      ≡ (wordParikh cmap (x ∷ [])) +v wordParikh cmap uv
    subLetterSum = wordParikhPlus cmap (x ∷ []) uv
    subX : (wordParikh cmap ( (x ∷ u) Data.List.++ v )) 
      ≡ (wordParikh cmap (x ∷ [])) +v wordParikh cmap uv
    subX = subst (λ y → wordParikh cmap y ≡ wordParikh cmap (x ∷ []) +v wordParikh cmap uv) listConcat subLetterSum
    subUV : (wordParikh cmap ( (x ∷ u) Data.List.++ v )) 
      ≡ (wordParikh cmap (x ∷ [])) +v puv
    subUV = subst (λ y → wordParikh cmap ((x ∷ u) Data.List.++ v) ≡
                           wordParikh cmap (x ∷ []) +v y) subSum subX

    vecAssoc : (wordParikh cmap (x ∷ [])) +v (wordParikh cmap u +v (wordParikh cmap v)) 
             ≡ (wordParikh cmap (x ∷ []) +v wordParikh cmap u) +v (wordParikh cmap v) 
    vecAssoc = sym vAssoc 
    uxSub : (wordParikh cmap ( (x ∷ u) Data.List.++ v )) 
             ≡ (wordParikh cmap (x ∷ []) +v wordParikh cmap u) +v (wordParikh cmap v) 
    uxSub  = trans subUV vecAssoc
    uxPar :  wordParikh cmap (x ∷ u) ≡ wordParikh cmap (x ∷ []) +v wordParikh cmap u
    uxPar = ? 
  
  in {!!}
    where
      _++l_ = Data.List._++_

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



