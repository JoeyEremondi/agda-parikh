module REMatch where

open import Data.Char
import Data.Nat
open import Data.List
open import Data.Bool

open import Data.Product


open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

{-
data Nullable? : Set where
  Nullable : Nullable?
  NonNull : Nullable?


nullTop : Nullable? -> Nullable? -> Nullable?
nullTop Nullable Nullable = Nullable
nullTop _ _ = NonNull

nullBottom : Nullable? -> Nullable? -> Nullable?
nullBottom NonNull NonNull = NonNull
nullBottom _ _ = Nullable
-}

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

accept : RE -> List Char -> Bool
accept r s = acc r s null

data REMatch : List Char -> RE -> Set where
  EmptyMatch : REMatch [] ε
  LitMatch : (c : Char) -> REMatch (c ∷ []) (Lit c)
  LeftPlusMatch : 
    {s : List Char} {r1 : RE} {r2 : RE} 
    -> REMatch s r1 
    -> REMatch s (r1 + r2)  
  RightPlusMatch : 
    {s : List Char} {r1 : RE} {r2 : RE} 
    -> REMatch s r2 
    -> REMatch s (r1 + r2)
  ConcatMatch : 
    {s1 : List Char} {s2 : List Char} {r1 : RE} {r2 : RE}
    -> REMatch s1 r1
    -> REMatch s2 r2
    -> REMatch (s1 ++ s2) (r1 · r2)
  EmptyStarMatch : {r : RE} -> REMatch [] (r *)
  StarMatch : 
    {s1 : List Char} {s2 : List Char } {r : RE}
    -> REMatch s1 r
    -> REMatch s2 (r *)
    -> REMatch (s1 ++ s2) (r *)

orLemma1 : {x : Bool} {y : Bool} -> (y ≡ true) -> (y ∨ x) ≡ true
orLemma1 {x} {true} pf = refl
orLemma1 {x} {false} ()

{-
orCommut : {x : Bool} {y : Bool} -> (y ∨ x) ≡ (x ∨ y)
orCommut {true} {true} = refl
orCommut {false} {true} = refl
orCommut {true} {false} = refl
orCommut {false} {false} = refl
-}

orLemma2 : {x : Bool} {y : Bool} -> (y ≡ true) -> (x ∨ y) ≡ true
orLemma2 {true} {true} pf = refl
orLemma2 {false} {true} pf = refl
orLemma2 {true} {false} pf = refl
orLemma2 {false} {false} ()


accCorrect : 
  (r : RE) (s : List Char) (s1 : List Char) (s2 : List Char) (k : (List Char -> Bool)) 
  -> ( (s1 ++ s2) ≡ s)
  -> (REMatch s1 r)
  -> (k s2 ≡ true)
  -> (acc r s k ≡ true )
--accCorrect ∅ [] [] [] k _ () kproof 
accCorrect ε  [] ._ []  k _ EmptyMatch kproof = kproof
--accCorrect (r1 + r2) s s1 s2 k splitProof _ kproof = {!!}  
--accCorrect {_ · _}{s}{s1}{s2}{k} 
accCorrect (.r1 · .r2 ) s ._ s2  k  splitProof (ConcatMatch {s1'} {s2'} {r1} {r2} subMatch1 subMatch2) kproof  = 
  let
    newK = (λ s' → acc r2 s' k)
    newKproof : (newK s2 ≡ true)
    newKproof = {!!}
    subCorrect2 = {!!} -- accCorrect r2 s2 ? ? ? subMatch2 ?
    subCorrect1 = accCorrect r1 (s1' ++ s2' ) s1' s2' (λ s' -> acc r2 s' k) refl subMatch1 subCorrect2
  in {!-t 100!}
accCorrect (.r1 + .r2 ) s .s1 s2  k  
  splitProof (LeftPlusMatch {s1} {r1} {r2} subMatch) kproof  = 
   orLemma1 (accCorrect r1 s s1 s2 k splitProof subMatch kproof )
accCorrect (.r1 + .r2) s .s1 s2  k  
  splitProof (RightPlusMatch {s1} {r1} {r2} subMatch) kproof  =
    let subCorrect = accCorrect r2 s s1 s2 k splitProof subMatch kproof
    in orLemma2 {acc r1 s k} {acc r2 s k} subCorrect
--accCorrect (.r *) [] [] [] k _ (EmptyStarMatch {r}) kproof = kproof
accCorrect (.r *) s ._ s2 k _ (StarMatch {s1'} {s1''} {r} sub1 sub2) kproof = {!!}
accCorrect _ _ _ _ _ _ _ _ = {!!}

{-
matchCorrect : (s : List Char) (r : RE) -> ((accept r s) ≡ true) -> REMatch s r
matchCorrect _ ∅ ()
matchCorrect [] ε _ = EmptyMatch
matchCorrect (_ ∷ _) ε ()
matchCorrect s (r1 + r2) pf  with accept r1 s | accept r2 s
matchCorrect s (r1 + r2) pf | true | _ = LeftPlusMatch s r1 r2 (matchCorrect s r1 refl)
matchCorrect s (r1 + r2) pf | _ | true = {!!}
matchCorrect s (r1 + r2) () | false | false
{-
  if (accept r1 s) 
  then LeftPlusMatch s r1 r2 (matchCorrect s r1 refl)
  else RightPlusMatch s r1 r2 (matchCorrect s r2 refl)-}
  

matchCorrect s r match = {!!}
-}
