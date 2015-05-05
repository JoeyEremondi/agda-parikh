module REMatch where

open import Data.Char
import Data.Nat
open import Data.List
open import Data.Bool

data Nullable? : Set where
  Nullable : Nullable?
  NonNull : Nullable?

nullTop : Nullable? -> Nullable? -> Nullable?
nullTop Nullable Nullable = Nullable
nullTop _ _ = NonNull

nullBottom : Nullable? -> Nullable? -> Nullable?
nullBottom NonNull NonNull = NonNull
nullBottom _ _ = Nullable

data RE : Nullable? -> Set where
  ε : RE Nullable
  ∅ : RE NonNull
  Lit : Char -> RE NonNull
  _+_ : {n1 : Nullable? }{n2 : Nullable? } -> (RE n1) -> (RE n2) -> RE (nullBottom n1 n2)
  _·_ : {n1 : Nullable? }{n2 : Nullable? } -> (RE n1) -> (RE n2) -> RE (nullTop n1 n2)
  _* : RE NonNull -> RE Nullable
  

mutual

--  starMatch : RE NonNull -> List Char -> List Char -> (List Char -> Bool) -> Bool
--  starMatch r s₁ s₂ k = (acc r s₁ k ) ∧ (acc (r *) s₂ k) 

  acc : {n : Nullable? } -> RE n -> List Char -> (List Char -> Bool) -> Bool
  acc ε s k = k s
  acc ∅ _ _ = false
  acc (Lit _) [] _ = false
  acc (Lit c) (sFirst ∷ sRest) k = if (c == sFirst) then (k sRest) else false 
  acc (r₁ + r₂) s k = (acc r₁ s k) ∨ (acc r₂ s k)
  acc (r₁ · r₂) s k = acc r₁ s (λ s' -> acc r₂ s' k)
  acc (r *) [] k = (k [])  
  acc (r *) cs k = k cs ∨ acc r cs (\cs' -> acc r cs' k)
  --acc (r *) (sFirst ∷ sRest) k =  starMatch r (sFirst ∷ [] ) sRest k
