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

data RE :  Set where
  ε : RE 
  ∅ : RE 
  Lit : Char -> RE 
  _+_ : RE -> RE -> RE
  _·_ :  RE -> RE -> RE
  _* : RE -> RE
  

acc :  RE -> List Char -> (List Char -> Bool) -> Bool
acc ε s k = k s
acc ∅ _ _ = false
acc (Lit _) [] _ = false
acc (Lit c) (sFirst ∷ sRest) k = if (c == sFirst) then (k sRest) else false 
acc (r₁ + r₂) s k = (acc r₁ s k) ∨ (acc r₂ s k)
acc (r₁ · r₂) s k = acc r₁ s (λ s' -> acc r₂ s' k)
acc (r *) [] k = (k [])  
acc (r *) cs k = k cs ∨ acc r cs (\cs' -> acc r cs' k)
  --acc (r *) (sFirst ∷ sRest) k =  starMatch r (sFirst ∷ [] ) sRest k

data REMatch : List Char -> RE -> Set where
  EmptyMatch : REMatch [] ε
  LitMatch : (c : Char) -> REMatch (c ∷ []) (Lit c)
  LeftPlusMatch : 
    (s : List Char) (r1 : RE) (r2 : RE) 
    -> REMatch s r1 
    -> REMatch s (r1 + r2)  
  RightPlusMatch : 
    (s : List Char) (r1 : RE) (r2 : RE) 
    -> REMatch s r2 
    -> REMatch s (r1 + r2)
  ConcatMatch : 
    (s1 : List Char) (s2 : List Char ) (r1 : RE) (r2 : RE)
    -> REMatch s1 r1
    -> REMatch s2 r2
    -> REMatch (s1 ++ s2) (r1 · r2)
  EmptyStarMatch : (r : RE) -> REMatch [] (r *)
  StarMatch : 
    (s1 : List Char) (s2 : List Char ) (r : RE)
    -> REMatch s1 r
    -> REMatch s2 (r *)
    -> REMatch (s1 ++ s2) (r *)
