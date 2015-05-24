module SemiLin where

open import Data.Vec
open import Data.Nat
open import Data.List

open import Data.Product


-- n-dimensional Vectors of natural numbers
NatVec : ℕ -> Set
NatVec n = Vec ℕ n

--Scalar multiplication
_·ₛ_ : {n : ℕ} -> ℕ -> NatVec n -> NatVec n
c ·ₛ v = ?

--A linear set is defined entirely by a pair of vectors
--(u,v) represents the set { cu + v | c ∈ ℕ} of n-dimensional vectors 
LinSet : ℕ -> Set
LinSet n = (NatVec n) × (NatVec n)


--A semi-linear set can be represented by a finite list of linear sets
--TODO should this be vectors, to ensure finite?
SemiLinSet : ℕ -> Set
SemiLinSet n = List (LinSet n)

--Witnesses for Membership in linear and semi-linear sets
data InLinear : {n : ℕ} -> (v : NatVec n) -> LinSet n -> Set where
  withScalar : {n : ℕ} -> (v : NatVec n) -> (s : LinSet n) -> InLinear v s 
