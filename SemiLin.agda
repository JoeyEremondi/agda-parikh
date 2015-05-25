module SemiLin where

open import Data.Vec
open import Data.Nat
import Data.Fin as Fin

open import Data.List
open import Data.Bool
open import Data.Char

open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.Core

open import Category.Monad

import RETypes


--Maps each character in a list to a natural number
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

--Prove that 0 is an identity
v0identLeft : {n : ℕ} -> {v : Parikh n} -> v0 +v v ≡ v
v0identLeft {v = []} = refl
v0identLeft {v = x ∷ v} = 
  let
    subIdent = v0identLeft {v = v}
  in cong (λ t → x ∷ t) subIdent



--A linear set is defined entirely by a pair of vectors
--(u,v) represents the set { cu + v | c ∈ ℕ} of n-dimensional vectors 
LinSet : ℕ -> Set
LinSet n = (Parikh n) × (∃ λ (m : ℕ) → Vec (Parikh n) m )


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

--A semi-linear set can be represented by a finite list of linear sets
--TODO should this be vectors, to ensure finite?
SemiLinSet : ℕ -> Set
SemiLinSet n = List (LinSet n)
{-
--Witnesses for Membership in linear and semi-linear sets
data InLinear : {n : ℕ} -> (v : Parikh n) -> LinSet n -> Set where
  withScalar : {n : ℕ} 
    -> (v : Parikh n) 
    -> ( l : LinSet n)
    -> (∃ (λ (c : ) -> v ≡ (c ·ₛ (proj₁ s) ) +v (proj₂ s) ))
    -> InLinear v s
-}
--Basically just a proof that there's some element of the list containing the vector
data InSemiLin : {n : ℕ} -> (v : Parikh n) -> (sl : SemiLinSet n) -> Set where
  inHead : {n : ℕ} 
    -> (v : Parikh n) 
    -> (sh : LinSet n) 
    -> (st : SemiLinSet n)
--    -> InLinear v sh
    -> InSemiLin v (sh ∷ st)
  inTail : {n : ℕ} 
    -> (v : Parikh n) 
    -> (sh : LinSet n) 
    -> (st : SemiLinSet n)
    -> InSemiLin v st
    -> InSemiLin v (sh ∷ st)


{-
--Sum each linear set in the two semi-linear sets
_+s_ : {n : ℕ} -> SemiLinSet n -> SemiLinSet n -> SemiLinSet n
s1 +s s2 = Data.List.concat (Data.List.map (λ l1 -> Data.List.map (λ l2 -> (proj₁ l1 +v proj₁ l2 , proj₂ l1 +v proj₂ l2 )  ) s2 ) s1)

--Creates a  vector
--Which has 1 in the specified component, and 0 elsewhere
basis : { n : ℕ} -> ( i : Fin.Fin n ) -> Parikh n
basis Fin.zero  = Data.Vec.[ suc zero ] Data.Vec.++ v0 
basis (Fin.suc f) = 0 ∷ basis f 

reSemiLin : {n : ℕ} {null? : RETypes.Null?} -> (Char -> Fin.Fin n) -> RETypes.RE null? -> SemiLinSet n  
reSemiLin cmap RETypes.ε = Data.List.[ v0 , v0 ]
reSemiLin cmap RETypes.∅ = []
reSemiLin cmap (RETypes.Lit x) = Data.List.[ v0 , basis (cmap x ) ]
reSemiLin cmap (r1 RETypes.+ r2) = reSemiLin cmap r1 Data.List.++ reSemiLin cmap r2
reSemiLin cmap (r1 RETypes.· r2) = reSemiLin cmap r1 +s reSemiLin cmap r2
reSemiLin cmap (r RETypes.*) = {!!}

-}
