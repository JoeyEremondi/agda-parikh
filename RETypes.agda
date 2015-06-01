module RETypes where

open import Data.Char
open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality



data Null? : Set where
  NonNull : Null?
  MaybeNull : Null?

data NullTop : Null? -> Null? -> Null? -> Set where
  BothNullT : NullTop MaybeNull MaybeNull MaybeNull
  LeftNullT : NullTop MaybeNull NonNull NonNull
  RightNullT : NullTop NonNull MaybeNull NonNull
  BothNonNullT : NullTop NonNull NonNull NonNull

data NullBottom : Null? -> Null? -> Null? -> Set where
  BothNullB : NullBottom NonNull NonNull NonNull
  LeftNullB : NullBottom MaybeNull NonNull NonNull
  RightNullB : NullBottom NonNull MaybeNull NonNull
  BothNonNullB : NullBottom MaybeNull MaybeNull MaybeNull

{-
nullTop : Null? -> Null? -> Null?
nullTop MaybeNull MaybeNull = MaybeNull
nullTop _ _ = NonNull

nullBottom : Null? -> Null? -> Null?
nullBottom NonNull NonNull = NonNull
nullBottom _ _ = MaybeNull
-}


--TODO when define this way, problem have function defined
--needs to unify with function type to figure out if there is branch
--Unifies with return type of RE
--Plus: unifies RE nullBottom with RE maybe
--Change last line of plus into
data RE : Null? -> Set where
  ε : RE MaybeNull
  ∅ : RE NonNull 
  Lit : Char -> RE NonNull 
  _+_ : {n1 n2 n3 : Null? } 
    -> {nb : NullBottom n1 n2 n3} 
    -> RE n1
    -> RE n2 
    -> RE n3
  _·_ :  {n1 n2 n3 : Null? } 
    -> {nt : NullTop n1 n2 n3} 
    -> RE n1
    -> RE n2 
    -> RE n3
  _* : RE NonNull -> RE MaybeNull



data REMatch : {n : Null?} -> List Char -> RE n -> Set where
  EmptyMatch : REMatch [] ε
  LitMatch : (c : Char) -> REMatch (c ∷ []) (Lit c)
  LeftPlusMatch : 
    {n1 n2 n3 : Null? } 
    -> {nb : NullBottom n1 n2 n3} 
    -> {s : List Char} {r1 : RE n1}  
    -> (r2 : RE n2)
    -> REMatch s r1 
    -> REMatch {n3} s (_+_ {n1} {n2} {n3} {nb} r1 r2)  
  RightPlusMatch : 
    {n1 n2 n3 : Null? } 
    -> {nb : NullBottom n1 n2 n3} 
    -> {s : List Char} -> (r1 : RE n1) -> {r2 : RE n2} 
    -> REMatch s r2 
    -> REMatch {n3} s (_+_ {n1} {n2} {n3} {nb} r1 r2)
  ConcatMatch : 
    {n1 n2 n3 : Null? } 
    -> {nt : NullTop n1 n2 n3} 
    -> {s1 s2 s3 : List Char} {spf : s1 ++ s2 ≡ s3} {r1 : RE n1} {r2 : RE n2}
    -> REMatch s1 r1
    -> REMatch s2 r2
    -> REMatch {n3} s3 (_·_ {n1} {n2} {n3} {nt} r1 r2)
  EmptyStarMatch : {r : RE NonNull} -> REMatch [] (r *)
  StarMatch : 
    {c1 : Char} {s1t : List Char} {s2 : List Char } {r : RE NonNull}
    -> REMatch (c1 ∷ s1t) r
    -> REMatch s2 (r *)
    -> REMatch ((c1 ∷ s1t) ++ s2) (r *)
