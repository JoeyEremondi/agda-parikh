{-
Joseph Eremondi
Utrecht University Capita Selecta
UU# 4229924
July 22, 2015
-}

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
open ≡-Reasoning

open import Utils

open import Function

import RETypes

open import Data.Sum

import Data.Nat.Properties.Simple



--The Parikh vector for a word is the count of occurrences of
--each letter of our alphabet in that word.
--We just represent this as a vector of Natural numbers
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

--0 times anything is v0
scalar0ident : {n : ℕ} -> (v : Parikh n ) -> 0 ·ₛ v ≡ v0
scalar0ident [] = refl
scalar0ident (x ∷ v) = cong (_∷_ zero) (scalar0ident v)  

--Prove that 0 is a neutral element on the left
v0identLeft : {n : ℕ} -> {v : Parikh n} -> v0 +v v ≡ v
v0identLeft {v = []} = refl
v0identLeft {v = x ∷ v} = 
  let
    subIdent = v0identLeft {v = v}
  in cong (λ t → x ∷ t) subIdent

--Prove that vector addition is commutative
v+-commut : {n : ℕ} -> (u : Parikh n) -> (v : Parikh n) -> (u +v v ≡ v +v u)
v+-commut [] [] = refl
v+-commut (x ∷ u) (y ∷ v) rewrite +-comm x y  | v+-commut u v = refl

--Prove the right-identity for vector addition with 0
--Just conbines commutativity and the left identity
v0identRight : {n : ℕ} -> {v : Parikh n} -> v +v v0 ≡ v
v0identRight {v = v} = 
  begin
    v +v v0
  ≡⟨ v+-commut v v0 ⟩
    v0 +v v 
  ≡⟨ v0identLeft ⟩ 
    v ∎ 


--Prove that vector addition is associative
--I couldn't figure out how to get this one working with rewrite
vAssoc : {n : ℕ} -> {x : Parikh n} {y : Parikh n} {z : Parikh n}
  -> (x +v y) +v z ≡ x +v (y +v z) 
vAssoc {zero} {[]} {[]} {[]} = refl
vAssoc {suc n} {xh ∷ xt} {yh ∷ yt} {zh ∷ zt} =
  let
    x = xh ∷ xt
    y = yh ∷ yt
    z = zh ∷ zt
  in --_≡⟨_⟩_
      begin
        (x +v y) +v z 
      ≡⟨ refl ⟩ 
        (xh + yh + zh) ∷ (xt +v yt) +v zt 
      ≡⟨ cong (λ h → h ∷ (xt +v yt) +v zt) (+-assoc xh yh zh) ⟩ 
        xh + (yh + zh) ∷ (xt +v yt) +v zt
      ≡⟨ cong (λ t → xh + (yh + zh) ∷ t) vAssoc ⟩ 
        (xh + (yh + zh) ∷ xt +v (yt +v zt)) 
      ≡⟨ refl ⟩ 
        x +v (y +v z) 
      ∎

-- Wouter: here's one definition using rewrite...
vAssoc2 : {n : ℕ} -> {x : Parikh n} {y : Parikh n} {z : Parikh n}
  -> (x +v y) +v z ≡ x +v (y +v z) 
vAssoc2 {x = []} {[]} {[]} = refl
vAssoc2 {x = x ∷ xs} {y ∷ ys} {z ∷ zs} rewrite +-assoc x y z | vAssoc {x = xs} {y = ys} {z = zs} 
  = refl



--Prove that scalar multiplication distributes over vector addition
scalarAssoc : {n : ℕ} -> (x y : ℕ ) -> (v : Parikh n) -> (x + y) ·ₛ v ≡  (x ·ₛ v) +v (y ·ₛ v)
scalarAssoc x y [] = refl
scalarAssoc x y (vfirst ∷ v) rewrite scalarAssoc x y v | distribʳ-*-+ vfirst x y = refl


--Handy lemma, prove that 0 + anything is 0
ident0 : (x : ℕ) -> x + 0 ≡ x
ident0 zero = refl
ident0 (suc x) = cong suc (ident0 x)

--Show that 1 is an identity for scalar multiplication
scalarIdent : {n : ℕ} -> (v : Parikh n) -> (1 ·ₛ v ≡ v )
scalarIdent [] = refl
scalarIdent (x ∷ v) rewrite scalarIdent v | ident0 x = refl

--A linear set is defined by an offset vector b
--And a set of m vectors v1 ... vm.
--A vector u is in a linear set if there exists constants c1 ... cm
--such that u = b + c1·v1 + ... + cm·vm 

-- Wouter -- do you really want to existentially quantify m?
-- You could also define LinSet n m = Parikh n × Vec (Parikh n) m
--  I don' think it makes a whole lot of difference, but later on in applyLinCom
--  you use this anyway.
--  For what it's worth, you may want to note that ∃ n . Vec a n is isomorphic to List a
LinSet : ℕ -> Set
LinSet n = (Parikh n) × (∃ λ (m : ℕ) → Vec (Parikh n) m )



--Given an offset vector, a set of m Parikh vectors, and a set of m constants
--Return b + c1·v1 + ... + cm·vm
-- Wouter: you might want to consider defining this directly by recursion over the 
--  cs and vset. The induction you use in this definition will determine how easy/hard
--  it might be to reason about this function later.
--  See the proof of sumPreserved in SemiLinRE, for instance.
applyLinComb : {n : ℕ} -> Parikh n -> (m : ℕ ) -> (Vec (Parikh n) m ) -> Vec ℕ m ->  Parikh n
applyLinComb base .0 [] cs = base
applyLinComb base (suc m) (firstVec ∷ vset) (firstConst ∷ cs) = (firstConst ·ₛ firstVec) +v (applyLinComb base m vset cs)


--Show that, if all the coefficients in a linear combination are 0, that the resulting vector is the base (offset) vector
v0apply : {n m : ℕ} -> (base : Parikh n) -> (vecs : Vec (Parikh n) m ) -> applyLinComb base m  vecs (v0 {m}) ≡ base 
v0apply base [] = refl
v0apply {n} {suc m} base (x ∷ vecs) rewrite scalar0ident x | v0apply base vecs = v0identLeft


--A type acting as a witness that a vector is in a linear set
--Is just a set of coefficients, and a proof that those coefficients
--form v as a linear combination of vectors in our linear set's list
LinComb : {n : ℕ} -> Parikh n -> LinSet n -> Set
LinComb {n} initV (base , m , vset)  = 
  ∃ (λ (cs : Vec ℕ m) -> applyLinComb base m vset cs ≡ initV )


--Sum of each vector in a linear set i.e. L1 + L2 = {x + y | x in L1, y in L2 }
--We just add the bases, and concatenate the list of vectors which can be multiplied by constants
_+l_ : {n : ℕ} -> LinSet n -> LinSet n -> LinSet n
(base1 , m1 , vecs1 ) +l (base2 , m2 , vecs2 ) = (base1 +v base2 , m1 + m2 , vecs1 Data.Vec.++ vecs2 )


--A semi-linear is a finite union of linear sets
--We represent this using a list of linear sets
SemiLinSet : ℕ -> Set
SemiLinSet n = List (LinSet n)

--Sum each linear set in the two semi-linear sets
--We basically just do a pairwise +l for each linear set in each of the semi-linear sets
_+s_ : {n : ℕ} -> SemiLinSet n -> SemiLinSet n -> SemiLinSet n
s1 +s s2 = Data.List.concat (Data.List.map (λ l1 -> Data.List.map (λ l2 -> l1 +l l2 )  s2 ) s1 )


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



--Creates a  vector
--Which has 1 in the specified component, and 0 elsewhere
basis : { n : ℕ} -> ( i : Fin.Fin n ) -> Parikh n
basis Fin.zero  = Data.Vec.[ suc zero ] Data.Vec.++ v0 
basis (Fin.suc f) = 0 ∷ basis f 


--A proof that if a vector is in a SemiLinear set, then the vector is also in the 
--union of that SemiLinear set with another single linear set
slExtend : {n : ℕ} -> (v : Parikh n) -> (sl : SemiLinSet n) -> InSemiLin v sl -> (ls : LinSet n) -> InSemiLin v (ls ∷ sl )
slExtend v sl inTail ls = InTail v ls sl inTail


--the above proof, but extended to an arbitrary number of linear sets
slConcatLeft : {n : ℕ} -> (v : Parikh n) -> (sl : SemiLinSet n) -> InSemiLin v sl -> (sl2 : SemiLinSet n) -> InSemiLin v (sl2 Data.List.++  sl )
slConcatLeft v sl inTail [] = inTail
slConcatLeft v sl inTail (x ∷ sl2) = InTail v x (sl2 Data.List.++ sl) (slConcatLeft v sl inTail sl2)


--The above proof, but the vectors are concatenated on the right
slConcatRight : {n : ℕ} -> (v : Parikh n) -> (sl : SemiLinSet n) -> InSemiLin v sl -> (sl2 : SemiLinSet n) -> InSemiLin v (sl Data.List.++  sl2 )
slConcatRight v .(sh ∷ st) (InHead .v sh st x) sl2 = (InHead v sh (st Data.List.++ sl2) x)
slConcatRight v .(sh ∷ st) (InTail .v sh st inTail) sl2 = slExtend v (st Data.List.++ sl2) (slConcatRight v st inTail sl2) sh


--Show that, if a vector is in a linear-set, then it is in a semi-linear set containing that linear set
slCons :  {n : ℕ} -> (v : Parikh n) -> (sl : SemiLinSet n) -> (ls : LinSet n) -> (InSemiLin v (ls ∷ [] ) ) -> InSemiLin v (ls ∷ sl )
slCons v sl sh (InHead .v .sh .[] x) = InHead v sh sl x
slCons v sl sh (InTail .v .sh .[] ())




--A linear set containing only v0
l0 : {n : ℕ} -> LinSet n
l0 = (v0 , zero , [] )

--A semi-linear set containing only v0
s0 : {n : ℕ} -> SemiLinSet n
s0 = (v0 , zero , [] ) ∷ []


--Show that, if a vector is in s0, then it must be v0
s0match : {n : ℕ} -> (v : Parikh n) -> InSemiLin v s0 -> v ≡ v0
s0match .v0 (InHead .v0 .(v0 , 0 , []) .[] (comb , refl)) = refl
s0match v (InTail .v .(v0 , 0 , []) .[] ())




--Show that if a vector is in a semi-lin set, then it's not the empty list
inSemiNonEmtpy : {n : ℕ} -> (v : Parikh n) -> (s : SemiLinSet n) -> InSemiLin v s -> ∃ λ sh -> ∃ λ st -> s ≡ sh ∷ st
inSemiNonEmtpy v .(sh ∷ st) (InHead .v sh st x) = sh , st , refl
inSemiNonEmtpy v .(sh ∷ st) (InTail .v sh st inSemi) = sh , st , refl


-------------Functions for Star ------------------
-- Star is by far the most complicated case, so a large number of definitions and lemmas
--Are dedicated to it

--Given a linear set L, find another linear set
--such that L = L +l (L*)
--We do this by allowing the base to appear an arbitrary number of times
linStar : {n : ℕ} -> LinSet n -> LinSet n
linStar (base , m , vecs ) = (base , suc m , base ∷ vecs )

--Given a non-empty semi-linear set, find the sum of the star
--of all linear sets it contains
starSum : {n : ℕ} -> LinSet n -> SemiLinSet n -> LinSet n
starSum ls [] = linStar ls
starSum first (sh ∷ s) = (linStar sh) +l starSum first s

--The semi-linear set for the Star of a regular expression
--The semi-linear set always contains 0, since the empty string matches r*
--We then union s0 with the sum of the star of each linear set
--in the Parikh image of r 
starSemiLin : {n : ℕ} -> SemiLinSet n -> SemiLinSet n
starSemiLin [] = s0
starSemiLin (first ∷ s) = s0 Data.List.++ (  starSum first s ∷ [])


--Show that v0 is always in a star semi-linear set
zeroInStar : {n : ℕ} -> (s ss : SemiLinSet n) -> ss ≡ (starSemiLin s)  -> InSemiLin v0 ss
zeroInStar [] .((v0 , 0 , []) ∷ []) refl = InHead v0 (v0 , zero , []) [] ([] , refl)
zeroInStar (x ∷ s) .((v0 , 0 , []) ∷ starSum x s ∷ []) refl = InHead v0 (v0 , zero , []) (starSum x s ∷ []) ([] , refl)


--Show that if we sum two linear sets, then the number of vectors that can be combined
--is the sum of the number in each input set
linSetLen : {n : ℕ} -> (l1 l2 l3 : LinSet n) -> l1 +l l2 ≡ l3 -> (proj₁ (proj₂ l3)) ≡ (proj₁ (proj₂ l1)) + (proj₁ (proj₂ l2))
linSetLen (proj₁ , m1 , proj₂) (proj₃ , m2 , proj₄) .(proj₁ +v proj₃ , m1 + m2 , proj₂ Data.Vec.++ proj₄) refl = refl


--Useful lemma, suc x = x + 1
plusOneDef : ( x : ℕ) -> (suc x ≡ x + 1)
plusOneDef zero = refl
plusOneDef (suc x) = cong suc (plusOneDef x)


--Show that we can "remove" part of the base vector
--When making a linear combination
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


--If we have two linear combinations of vectors,
--That we can make it into a single combination of vectors
--By adding the bases, and concatenating the vector lists, and
-- concatenating the coefficient lists
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


--Extend the idea of distributivity to linear combinations
--Basically, the c1*v +v c2*v = (c1 +v c2 )*v, where * is element-wise product
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



--If a linear set has base 0, and u and v are both in that set, then u+v is as well
sumEqualVecs : {n : ℕ} -> (ls : LinSet n) -> (proj₁ ls ≡ v0) -> (u v : Parikh n) -> LinComb u ls -> LinComb v ls -> LinComb (u +v v) ls
sumEqualVecs (.v0 , m , vecs) refl .(applyLinComb v0 m vecs uconsts) .(applyLinComb v0 m vecs vconsts) (uconsts , refl) (vconsts , refl)  = 
  (uconsts +v vconsts) , applyCombSum vecs uconsts vconsts --applyCombSum {!!} {!!} vecs uconsts vconsts


--Show that the base vector of a linear set is always in that set, just set coefficients to 0
linContainsBase : {n : ℕ} -> (base : Parikh n) -> (m : ℕ ) -> (vecs : Vec (Parikh n) m ) -> applyLinComb base m vecs v0 ≡ base
linContainsBase base .0 [] = refl
linContainsBase base (suc m) (x ∷ vecs) rewrite linContainsBase base m vecs  = 
  begin 
  (zero ·ₛ x) +v base 
  ≡⟨ cong (λ y → y +v base) (scalar0ident x) ⟩
  v0 +v base 
  ≡⟨ v0identLeft ⟩ 
  (base ∎)


--Show that applying a linear combination with the base is just
--The base, plus the linear combination with v0 base
--Just a useful lemma for other proofs, basically uses associativity
linCombRemoveBase 
 :  {n : ℕ}
 -> (m : ℕ )
 -> (base : Parikh n )
 -> (vecs : Vec (Parikh n) m )
 -> (c : Parikh m)
 -> applyLinComb base m vecs c ≡ base +v applyLinComb v0 m vecs c
linCombRemoveBase {n} m base vecs c = 
  begin 
  applyLinComb base m vecs c 
  ≡⟨ cong (λ x → applyLinComb x m vecs c) (sym v0identRight) ⟩ 
  applyLinComb (base +v v0) m vecs c 
  ≡⟨ baseSplit base v0 m vecs c ⟩
  base +v applyLinComb v0 m vecs c ∎

--Show that only v0 is in a set with no vectors and v0 base
emptyCombZero : {n : ℕ} -> (v : Parikh n ) -> LinComb v (v0 , 0 , []) -> v ≡ v0
emptyCombZero .v0 ([] , refl) = refl


--Show that when we add two linear combinations of the same vectors together,
--We get a linear combination of those vectors, with an extra base left-over
linCombDecompBase 
 :  {n : ℕ}
 -> (m : ℕ )
 -> (base : Parikh n )
 -> (vecs : Vec (Parikh n) m )
 -> (c1 : Parikh m )
 -> (c2 : Parikh m)
 -> (applyLinComb base m vecs c1 ) +v (applyLinComb base m vecs c2 ) ≡ base +v applyLinComb base m vecs (c1 +v c2)
linCombDecompBase .0 base [] c1 c2 = refl
linCombDecompBase (suc m) base (vec1 ∷ vecs) (c ∷ c1) (cc ∷ c2) rewrite linCombDecompBase m base vecs c1 c2 | linCombRemoveBase m base vecs c1 | linCombRemoveBase m base vecs c2   = 
  begin 
  ((c ·ₛ vec1) +v (base +v applyLinComb v0 m vecs c1)) +v
    ((cc ·ₛ vec1) +v (base +v applyLinComb v0 m vecs c2)) 
  ≡⟨ cong (λ x → x +v ((cc ·ₛ vec1) +v (base +v applyLinComb v0 m vecs c2))) (sym vAssoc ) ⟩ 
  (((c ·ₛ vec1) +v base) +v applyLinComb v0 m vecs c1) +v
    ((cc ·ₛ vec1) +v (base +v applyLinComb v0 m vecs c2)) 
  ≡⟨ cong (λ x → (x +v applyLinComb v0 m vecs c1) +v ((cc ·ₛ vec1) +v (base +v applyLinComb v0 m vecs c2))) (v+-commut (c ·ₛ vec1) base) ⟩
  ((base +v (c ·ₛ vec1)) +v applyLinComb v0 m vecs c1) +v
    ((cc ·ₛ vec1) +v (base +v applyLinComb v0 m vecs c2)) 
  ≡⟨ cong (λ x → x +v ((cc ·ₛ vec1) +v (base +v applyLinComb v0 m vecs c2))) vAssoc ⟩
  (base +v ((c ·ₛ vec1) +v applyLinComb v0 m vecs c1)) +v
    ((cc ·ₛ vec1) +v (base +v applyLinComb v0 m vecs c2)) 
  ≡⟨ vAssoc ⟩
  base +v
    (((c ·ₛ vec1) +v applyLinComb v0 m vecs c1) +v
     ((cc ·ₛ vec1) +v (base +v applyLinComb v0 m vecs c2))) 
  ≡⟨ cong (λ x → base +v (((c ·ₛ vec1) +v applyLinComb v0 m vecs c1) +v x)) (sym vAssoc) ⟩ 
  base +v
    (((c ·ₛ vec1) +v applyLinComb v0 m vecs c1) +v
     (((cc ·ₛ vec1) +v base) +v applyLinComb v0 m vecs c2)) 
  ≡⟨ cong (λ x → base +v (((c ·ₛ vec1) +v applyLinComb v0 m vecs c1) +v (x +v applyLinComb v0 m vecs c2))) (v+-commut (cc ·ₛ vec1) base) ⟩
  base +v
    (((c ·ₛ vec1) +v applyLinComb v0 m vecs c1) +v
     ((base +v (cc ·ₛ vec1)) +v applyLinComb v0 m vecs c2)) 
  ≡⟨ cong (λ x → base +v x) vAssoc ⟩ 
  base +v
    ((c ·ₛ vec1) +v
     (applyLinComb v0 m vecs c1 +v
      ((base +v (cc ·ₛ vec1)) +v applyLinComb v0 m vecs c2))) 
  ≡⟨ cong (λ x → base +v ((c ·ₛ vec1) +v x)) (sym vAssoc) ⟩ 
  base +v
    ((c ·ₛ vec1) +v
     ((applyLinComb v0 m vecs c1 +v (base +v (cc ·ₛ vec1))) +v
      applyLinComb v0 m vecs c2)) 
  ≡⟨ cong (λ x → base +v ((c ·ₛ vec1) +v (x +v applyLinComb v0 m vecs c2))) (v+-commut (applyLinComb v0 m vecs c1) (base +v (cc ·ₛ vec1))) ⟩ 
  base +v
    ((c ·ₛ vec1) +v
     (((base +v (cc ·ₛ vec1)) +v applyLinComb v0 m vecs c1) +v
      applyLinComb v0 m vecs c2)) 
  ≡⟨ cong (λ x → base +v ((c ·ₛ vec1) +v x)) vAssoc ⟩ 
  base +v
    ((c ·ₛ vec1) +v
     ((base +v (cc ·ₛ vec1)) +v
      (applyLinComb v0 m vecs c1 +v applyLinComb v0 m vecs c2))) 
  ≡⟨ cong (λ x → base +v ((c ·ₛ vec1) +v ((base +v (cc ·ₛ vec1)) +v x))) (sym (applyCombSum vecs c1 c2)) ⟩ 
  base +v
    ((c ·ₛ vec1) +v
     ((base +v (cc ·ₛ vec1)) +v applyLinComb v0 m vecs (c1 +v c2))) 
  ≡⟨ cong (λ x → base +v x) (sym vAssoc) ⟩
  base +v
    (((c ·ₛ vec1) +v (base +v (cc ·ₛ vec1))) +v
     applyLinComb v0 m vecs (c1 +v c2)) 
  ≡⟨ cong (λ x → base +v (x +v applyLinComb v0 m vecs (c1 +v c2))) (sym vAssoc) ⟩ 
  base +v
    ((((c ·ₛ vec1) +v base) +v (cc ·ₛ vec1)) +v
     applyLinComb v0 m vecs (c1 +v c2)) 
  ≡⟨ cong (λ x → base +v ((x +v (cc ·ₛ vec1)) +v applyLinComb v0 m vecs (c1 +v c2))) (v+-commut (c ·ₛ vec1) base) ⟩ 
  base +v
    (((base +v (c ·ₛ vec1)) +v (cc ·ₛ vec1)) +v
     applyLinComb v0 m vecs (c1 +v c2)) 
  ≡⟨ cong (λ x → base +v (x +v applyLinComb v0 m vecs (c1 +v c2))) vAssoc ⟩ 
  base +v
    ((base +v ((c ·ₛ vec1) +v (cc ·ₛ vec1))) +v
     applyLinComb v0 m vecs (c1 +v c2)) 
  ≡⟨ cong (λ x → base +v ((base +v x) +v applyLinComb v0 m vecs (c1 +v c2))) (sym (scalarAssoc c cc vec1)) ⟩ 
  base +v
    ((base +v ((c + cc) ·ₛ vec1)) +v applyLinComb v0 m vecs (c1 +v c2)) 
  ≡⟨ cong (λ x → base +v (x +v applyLinComb v0 m vecs (c1 +v c2))) (v+-commut base ((c + cc) ·ₛ vec1)) ⟩ 
  base +v
    ((((c + cc) ·ₛ vec1) +v base) +v applyLinComb v0 m vecs (c1 +v c2)) 
  ≡⟨ cong (λ x → base +v x) vAssoc ⟩ 
  base +v
    (((c + cc) ·ₛ vec1) +v (base +v applyLinComb v0 m vecs (c1 +v c2))) 
  ≡⟨ cong (λ x → base +v (((c + cc) ·ₛ vec1) +v x)) (sym (baseSplit base v0 m vecs (c1 +v c2))) ⟩
  base +v
    (((c + cc) ·ₛ vec1) +v applyLinComb (base +v v0) m vecs (c1 +v c2)) 
  ≡⟨ cong (λ x → base +v (((c + cc) ·ₛ vec1) +v applyLinComb x m vecs (c1 +v c2))) v0identRight ⟩ 
  base +v (((c + cc) ·ₛ vec1) +v applyLinComb base m vecs (c1 +v c2)) 
  ≡⟨ cong (λ x → base +v x) refl ⟩ 
  (base +v (((c + cc) ·ₛ vec1) +v applyLinComb base m vecs (c1 +v c2)) ∎)


--Show that, if v1 is in L, and v2 is in L*, then v1 +v v2 is in L*
--Can be used to show that the sum of any vectors from L will be in L*
linStarExtend 
  : {n : ℕ} -> (v1 v2 : Parikh n ) ->
  (l1 ls : LinSet n ) -> ls ≡ linStar l1  -> LinComb v1 l1 -> LinComb v2 ls -> LinComb (v1 +v v2) ls
linStarExtend .(applyLinComb base m vecs c1) .((c2h ·ₛ base) +v applyLinComb base m vecs c2) (base , m , vecs) .(base , suc m , base ∷ vecs) refl (c1 , refl) (c2h ∷ c2 , refl)  =
  ((1 ∷ c1) +v (c2h ∷ c2)) , 
  (begin 
  (suc c2h ·ₛ base) +v applyLinComb base m vecs (c1 +v c2) 
  ≡⟨ cong (λ x → (x ·ₛ base) +v applyLinComb base m vecs (c1 +v c2)) refl  ⟩
  ((1 + c2h) ·ₛ base) +v applyLinComb base m vecs (c1 +v c2) 
  ≡⟨ cong (λ x → (x ·ₛ base) +v applyLinComb base m vecs (c1 +v c2)) (+-comm (suc zero) c2h) ⟩ 
  ((c2h + 1) ·ₛ base) +v applyLinComb base m vecs (c1 +v c2) 
  ≡⟨ cong (λ x → x +v applyLinComb base m vecs (c1 +v c2)) (scalarAssoc c2h 1 base) ⟩
  ((c2h ·ₛ base) +v (1 ·ₛ base)) +v
    applyLinComb base m vecs (c1 +v c2) 
  ≡⟨ cong (λ x → ((c2h ·ₛ base) +v x) +v applyLinComb base m vecs (c1 +v c2)) (scalarIdent base) ⟩ 
  ((c2h ·ₛ base) +v base) +v applyLinComb base m vecs (c1 +v c2) 
  ≡⟨ vAssoc ⟩
  (c2h ·ₛ base) +v (base +v applyLinComb base m vecs (c1 +v c2)) 
  ≡⟨ cong (λ x → (c2h ·ₛ base) +v x) (sym (linCombDecompBase m base vecs c1 c2)) ⟩ 
  (c2h ·ₛ base) +v
    (applyLinComb base m vecs c1 +v applyLinComb base m vecs c2) 
  ≡⟨ cong (λ x → (c2h ·ₛ base) +v x) (v+-commut (applyLinComb base m vecs c1) (applyLinComb base m vecs c2)) ⟩
  (c2h ·ₛ base) +v
    (applyLinComb base m vecs c2 +v applyLinComb base m vecs c1) 
  ≡⟨ sym vAssoc ⟩
  ((c2h ·ₛ base) +v applyLinComb base m vecs c2) +v
    applyLinComb base m vecs c1 
  ≡⟨ cong (λ x → x +v applyLinComb base m vecs c1 ) refl ⟩ 
  (applyLinComb base (suc m) (base ∷ vecs) (c2h ∷ c2)) +v
    applyLinComb base m vecs c1 
  ≡⟨ v+-commut ((c2h ·ₛ base) +v applyLinComb base m vecs c2) (applyLinComb base m vecs c1) ⟩ applyLinComb base m vecs c1 +v
              ((c2h ·ₛ base) +v applyLinComb base m vecs c2) ∎ 
  )


--Show that every non-empty vector in L* for a linear-set L
--Can be split into a vector from L and another in L*
--Basically proves that L* contains only sums of vectors in L
linStarDecomp
 :  {n : ℕ}
 -> (v : Parikh n)
 -> (l ls : LinSet n)
 -> v ≢ v0
 -> proj₁ (l) ≢ v0
 -> ls ≡ linStar l
 -> LinComb v ls
 -> LinComb v l ⊎ (∃ λ v1 -> ∃ λ v2 -> v1 +v v2 ≡ v × LinComb v1 l × LinComb v2 ls × v1 ≢ v0 ) 
linStarDecomp .((0 ·ₛ base) +v applyLinComb base m vecs c) (base , m , vecs) .(base , suc m , base ∷ vecs) vnz bnz refl (zero ∷ c , refl) rewrite scalar0ident base  = inj₁ (c , (sym v0identLeft))
linStarDecomp .((suc cbase ·ₛ base) +v applyLinComb base m vecs c) (base , m , vecs) .(base , suc m , base ∷ vecs) vnz bnz refl (suc cbase ∷ c , refl) = inj₂ ( base , (applyLinComb base (suc m) (base ∷ vecs) (cbase ∷ c)) , 
  (sym (begin -- ? ≡⟨ ? ⟩ ? 
    (suc cbase ·ₛ base) +v applyLinComb base m vecs c 
    ≡⟨ cong (λ x → x +v applyLinComb base m vecs c) refl ⟩ 
    ((1 + cbase) ·ₛ base) +v applyLinComb base m vecs c
    ≡⟨ cong (λ x → x +v applyLinComb base m vecs c) (scalarAssoc 1 cbase base) ⟩
    ((suc zero ·ₛ base) +v (cbase ·ₛ base)) +v
      applyLinComb base m vecs c 
    ≡⟨ cong (λ x → (x +v (cbase ·ₛ base)) +v applyLinComb base m vecs c) (scalarIdent base) ⟩ 
    (base +v (cbase ·ₛ base)) +v applyLinComb base m vecs c 
    ≡⟨  vAssoc ⟩ 
    base +v ((cbase ·ₛ base) +v applyLinComb base m vecs c) 
    ≡⟨ refl ⟩ 
    (base +v ((cbase ·ₛ base) +v applyLinComb base m vecs c) ∎))) ,
  (v0 , linContainsBase base m vecs) , ((cbase ∷ c) , refl) , bnz )





  



