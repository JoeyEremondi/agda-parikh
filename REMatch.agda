module REMatch where

open import Data.Char
import Data.Nat
--open import Data.List
open import Data.Bool

open import Data.Product

import Algebra
import Algebra.FunctionProperties

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.List
open import Data.List.Properties

open import Data.Sum

open List-solver renaming (nil to :[]; _⊕_ to _:++_; _⊜_ to _:≡_; solve to listSolve; prove to listProve)


data Null? : Set where
  NonNull : Null?
  MaybeNull : Null?

nullTop : Null? -> Null? -> Null?
nullTop MaybeNull MaybeNull = MaybeNull
nullTop _ _ = NonNull

nullBottom : Null? -> Null? -> Null?
nullBottom NonNull NonNull = NonNull
nullBottom _ _ = MaybeNull




data RE : Null? -> Set where
  ε : RE MaybeNull
  ∅ : RE NonNull 
  Lit : Char -> RE NonNull 
  _+_ : {n1 : Null? } -> {n2 : Null?} -> RE n1 -> RE n2 -> RE (nullBottom n1 n2)
  _·_ :  {n1 : Null? } -> {n2 : Null?} -> RE n1 -> RE n2 -> RE (nullTop n1 n2)
  _* : RE NonNull -> RE MaybeNull

listDivisions : List Char -> List (List Char × List Char)
listDivisions [] = ( [] , []) ∷ []
listDivisions (h ∷ t) = ([] , h ∷ t ) ∷ (Data.List.map (λ p -> ( (h ∷ proj₁ p) , proj₂ p )) (listDivisions t) ) 
  
elementMatches : {A : Set} (f : A -> Bool) -> List A -> Bool
elementMatches f [] = false
elementMatches f (h ∷ t) = (f h) ∨ elementMatches f t

mutual

  starMatch : {n : Null?} -> (RE n) -> List Char -> List Char -> (List Char -> Bool) -> Bool
  starMatch (r *) s1 (sh ∷ st) k =  (acc r (s1 ++ Data.List.[ sh ]) null ∧ acc ( r *) st k )  ∨ starMatch (r *) (s1 ++ Data.List.[ sh ]) st k
  starMatch (r *) s1 [] k = false
  starMatch _ _ _ _ = false

  acc :  {n : Null?} -> RE n -> List Char -> (List Char -> Bool) -> Bool
  acc ε s k = k s
  acc ∅ _ _ = false
  acc (Lit _) [] _ = false
  acc (Lit c) (sFirst ∷ sRest) k with (c Data.Char.≟ sFirst)
  ... | yes pf  = (k sRest)
  ... | no _  = false
  acc (r₁ + r₂) s k = (acc r₁ s k) ∨ (acc r₂ s k)
  acc (r₁ · r₂) s k = acc r₁ s (λ s' -> acc r₂ s' k)
  acc (r *) [] k = (k [])  
  acc (r *) (ch ∷ ct) k = 
    let
      cs = ch ∷ ct
    in k cs ∨ starMatch r [] cs k
    --acc r cs (\cs' -> acc (r) cs' k)
    --acc (r *) (sFirst ∷ sRest) k =  starMatch r (sFirst ∷ [] ) sRest k

accept : {n : Null?} -> RE n -> List Char -> Bool
accept r s = acc r s null

data REMatch : {n : Null?} -> List Char -> RE n -> Set where
  EmptyMatch : REMatch [] ε
  LitMatch : (c : Char) -> REMatch (c ∷ []) (Lit c)
  LeftPlusMatch : 
    {n1 : Null?} {n2 : Null?} {s : List Char} {r1 : RE n1} {r2 : RE n2} 
    -> REMatch s r1 
    -> REMatch s (r1 + r2)  
  RightPlusMatch : 
    {n1 : Null?} {n2 : Null?} {s : List Char} {r1 : RE n1} {r2 : RE n2} 
    -> REMatch s r2 
    -> REMatch s (r1 + r2)
  ConcatMatch : 
    {n1 : Null?} {n2 : Null?} {s1 : List Char} {s2 : List Char} {r1 : RE n1} {r2 : RE n2}
    -> REMatch s1 r1
    -> REMatch s2 r2
    -> REMatch (s1 ++ s2) (r1 · r2)
  EmptyStarMatch : {r : RE NonNull} -> REMatch [] (r *)
  StarMatch : 
    {s1 : List Char} {s2 : List Char } {r : RE NonNull}
    -> REMatch s1 r
    -> REMatch s2 (r *)
    -> REMatch (s1 ++ s2) (r *)

orLemma1 : {x : Bool} {y : Bool} -> (y ≡ true) -> (y ∨ x) ≡ true
orLemma1 {x} {true} pf = refl
orLemma1 {x} {false} ()

andElim1 : {x : Bool} {y : Bool} -> (x ∧ y) ≡ true -> (x ≡ true)
andElim1 {true} pf = refl
andElim1 {false} ()

andElim2 : {x : Bool} {y : Bool} -> (x ∧ y) ≡ true -> (y ≡ true)
andElim2 {y = true} pf = refl
andElim2 {y = false} () 

andCombine : {x : Bool} {y : Bool} -> x ≡ true -> y ≡ true -> (x ∧ y) ≡ true
andCombine {true} pfx pfy = pfy
andCombine {false} ()

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

orCases : {x : Bool} {y : Bool} -> (x ∨ y ≡ true) -> (x ≡ true) ⊎ (y ≡ true)
orCases {true} y = inj₁ refl
orCases {false} y = inj₂ y

accCorrect : 
  {n : Null? }
  (r : RE n) 
  (s : List Char) (s1 : List Char) (s2 : List Char) 
  (k : (List Char -> Bool)) 
  -> ( (s1 ++ s2) ≡ s)
  -> (REMatch s1 r)
  -> (k s2 ≡ true)
  -> (acc r s k ≡ true )
--accCorrect ∅ [] [] [] k _ () kproof 
accCorrect ε  [] ._ []  k _ EmptyMatch kproof = kproof
accCorrect (Lit .c) (c1 ∷ srest ) (.c ∷ []) s2 k _ (LitMatch c) kproof =
  let
    x = {!!}
  in {!!} 
accCorrect (.r1 · .r2 ) s ._ s2  k  splitProof (ConcatMatch {_} {_} {s1'} {s2'} {r1} {r2} subMatch1 subMatch2) kproof  = 
  let
           s1 = s1' ++ s2'
           split1 : s1 ++ s2 ≡ s
           split1 = splitProof
           split2 : (s1' ++ s2') ≡ s1 
           split2 = refl
           split3 : (s1' ++ s2') ++ s2 ≡ s1 ++ s2
           split3 = cong (λ x -> x ++ s2) split2
           split4 : (s1' ++ s2') ++ s2 ≡ s1' ++ s2' ++ s2
           split4 = {!!}
           --split4 = ? 
           --split4 : s1' ++ s2' ++ s2 ≡ s
           --split4 = trans split3 split1
           --assocThm = Algebra.Monoid.assoc Data.List.monoid
  in accCorrect r1 s s1' (s2' ++ s2) (\cs -> acc r2 cs k) {!!} --(listProve {!!} {!!}) {-(s1' :++ s2' :++ s2 :≡ s)-}
    subMatch1 
    (accCorrect r2 (s2' ++ s2) s2' s2 k refl subMatch2 kproof)
accCorrect (.r1 + .r2 ) s .s1 s2  k  
  splitProof (LeftPlusMatch {_} {_} {s1} {r1} {r2} subMatch) kproof  = 
   orLemma1 (accCorrect r1 s s1 s2 k splitProof subMatch kproof )
accCorrect (.r1 + .r2) s .s1 s2  k  
  splitProof (RightPlusMatch {_} {_} {s1} {r1} {r2} subMatch) kproof  =
    let subCorrect = accCorrect r2 s s1 s2 k splitProof subMatch kproof
    in orLemma2 {acc r1 s k} {acc r2 s k} subCorrect
accCorrect (.r *) [] ._ [] k _ (EmptyStarMatch {r}) kproof = kproof

accCorrect (r *) (sh ∷ st) [] s2 k sp1 _ kproof = 
  let
    s = sh ∷ st
    sp2 : s2 ≡ s
    sp2 = sp1
    kproof2 : k s ≡ k s2
    kproof2 = cong k (sym sp1)
    kproof3 : k s ≡ true
    kproof3 = trans kproof2 kproof
    orProof : (k s ∨ starMatch r [] s k) ≡ true
    orProof = orLemma1 kproof3
  in orProof
--accCorrect  (.r *) s ._ s2 k sp1 (StarMatch {s1'} {s1''} {r} sub1 sub2) kproof = ?
accCorrect ∅ _ _ _ _ _ ()
accCorrect ε (_ ∷ _ ) _ _ _ () _
accCorrect _ [] (_ ∷ _ ) _ _ () _ _
accCorrect _ [] _ (_ ∷ _ ) _ () _ _
accCorrect (Lit _) [] _ _ _ () _ _
accCorrect _ _ _ _ _ _ _ _ = {!!}



boolExclMiddle : {x : Bool} { y : Bool } -> (x ∨ y ≡ true ) -> (x ≡ false) -> (y ≡ true)
boolExclMiddle {true} p1 () 
boolExclMiddle {false} p1 p2 = p1



accComplete :
  {n : Null?}
  (r : RE n) 
  (s : List Char)
  (k : (List Char -> Bool))
  -> (acc r s k ≡ true)
  -> ∃ (λ s1 -> ∃ (λ s2 -> (s1 ++ s2 ≡ s) × ( k s2 ≡ true) × (REMatch s1 r ) ) ) 
accComplete ε [] k pf =  [] , [] , refl , pf , EmptyMatch
accComplete ε s k pf = [] , s , refl , pf , EmptyMatch
accComplete (Lit c) (c1 ∷ srest) k accProof with (c Data.Char.≟ c1)
...| yes eqProof =  
    let
      charsEqual : c ≡ c1
      charsEqual = eqProof
    in  Data.List.[ c ] , srest , cong (λ x → x ∷ srest) charsEqual , accProof , LitMatch c
accComplete (Lit c) (c1 ∷ srest) k () | no _
accComplete (r1 · r2) s k pf = 
  let
    sub1 : acc r1 s (λ s' -> acc r2 s' k) ≡ true
    sub1 = pf
    s11 , s2' , psub1 , psub2 , match1  = accComplete r1 s (λ s' -> acc r2 s' k) pf
    s12 , s2 , p1 , p2 , match2 = accComplete r2 s2' k psub2
    localAssoc :  s11 ++ (s12 ++ s2) ≡ (s11 ++ s12) ++ s2
    localAssoc = {!!}
    subProof1 : s11 ++ s2' ≡ s11 ++ (s12 ++ s2)
    subProof1 = sym ( cong (λ x -> s11 ++ x) p1 )
    subProof2 : s11 ++ s2' ≡ (s11 ++ s12) ++ s2 
    subProof2 = trans subProof1 localAssoc
    stringProof = trans (sym subProof2) psub1
  in (s11 ++ s12 ) , s2 , stringProof , p2 , (ConcatMatch match1 match2)
  
accComplete (r1 + r2) s k accProof with (orCases accProof)
...  | inj₁ leftTrue  = 
  let
    s1 , s2 , p1 , p2 , match = accComplete r1 s k leftTrue
  in s1 , s2 , p1 , p2 , LeftPlusMatch match
...  | inj₂ rightTrue  = let
    s1 , s2 , p1 , p2 , match = accComplete r2 s k rightTrue
  in s1 , s2 , p1 , p2 , RightPlusMatch match
accComplete (r *) [] k pf =  [] , [] , refl , pf , EmptyStarMatch
accComplete (r *) (sh ∷ st) k accProof with (orCases accProof)
... | inj₁ leftTrue  =  [] , (sh ∷ st) , refl , leftTrue , EmptyStarMatch
... | inj₂ rightTrue  =  {!!} , {!!} , {!!} , {!!} , {!!}
accComplete ∅ _ _ ()
accComplete (Lit _) [] _ ()
--accComplete _ _ _ _ = {!!}  


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
