module RETypes where

open import Data.Char
open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality



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
  _+_ : {n1 : Null? } {n2 : Null?} 
    -> RE n1
    -> RE n2 
    -> RE (nullBottom n1 n2)
  _·_ :  {n1 : Null? } {n2 : Null?}
    -> RE n1 
    -> RE n2 
    -> RE (nullTop n1 n2)
  _* : RE NonNull -> RE MaybeNull



data REMatch : {n : Null?} -> List Char -> RE n -> Set where
  EmptyMatch : REMatch [] ε
  LitMatch : (c : Char) -> REMatch (c ∷ []) (Lit c)
  LeftPlusMatch : 
    {n1 : Null?} {n2 : Null?} {s : List Char} {r1 : RE n1}  
    -> (r2 : RE n2)
    -> REMatch s r1 
    -> REMatch {nullBottom n1 n2} s (_+_ {n1} {n2} r1 r2)  
  RightPlusMatch : 
    {n1 : Null?} {n2 : Null?} {s : List Char} -> (r1 : RE n1) -> {r2 : RE n2} 
    -> REMatch s r2 
    -> REMatch {nullBottom n1 n2} s (r1 + r2)
  ConcatMatch : 
    {n1 : Null?} {n2 : Null?} {s1 : List Char} {s2 : List Char} {r1 : RE n1} {r2 : RE n2}
    -> REMatch s1 r1
    -> REMatch s2 r2
    -> REMatch {nullTop n1 n2} (s1 ++ s2) (r1 · r2)
  EmptyStarMatch : {r : RE NonNull} -> REMatch [] (r *)
  StarMatch : 
    {c1 : Char} {s1t : List Char} {s2 : List Char } {r : RE NonNull}
    -> REMatch (c1 ∷ s1t) r
    -> REMatch s2 (r *)
    -> REMatch ((c1 ∷ s1t) ++ s2) (r *)
