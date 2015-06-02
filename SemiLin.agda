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

open import Data.Nat.Properties.Simple

import RETypes

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
constMultLin : { n : ℕ} -> LinSet n -> LinSet n
constMultLin (base , m , vecs ) = v0 , suc m , base ∷ vecs


--The algorithm mapping regular expressions to the Parikh set of
--the language matched by the RE
--We prove this correct below
reSemiLin : {n : ℕ} {null? : RETypes.Null?} -> (Char -> Fin.Fin n) -> RETypes.RE null? -> SemiLinSet n 
reSemiLin cmap RETypes.ε = Data.List.[ v0 , 0 , [] ]
reSemiLin cmap RETypes.∅ = []
reSemiLin cmap (RETypes.Lit x) = Data.List.[ basis (cmap x ) , 0 , [] ]
reSemiLin cmap (r1 RETypes.+ r2) = reSemiLin cmap r1 Data.List.++ reSemiLin cmap r2
reSemiLin cmap (r1 RETypes.· r2) = reSemiLin cmap r1 +s reSemiLin cmap r2
reSemiLin cmap (r RETypes.*) = Data.List.map (constMultLin ) (reSemiLin cmap r)

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
    subSum : wordParikh cmap (u Data.List.++ v) ≡ (wordParikh cmap u) +v (wordParikh cmap v)
    subSum = wordParikhPlus cmap u v
    charBasis : wordParikh cmap Data.List.[ x ] ≡ basis (cmap x)
    charBasis = v0identRight
    listConcat : ((x ∷ u) Data.List.++ v ) ≡ [ x ] Data.List.++ ( (u Data.List.++ v) )
  in {!!}

reParikhCorrect : 
  {n : ℕ} 
  -> {null? : RETypes.Null?} 
  -> (cmap : Char -> Fin.Fin n) 
  -> (r : RETypes.RE null?) 
  -> (w : List Char ) 
  -> RETypes.REMatch w r
  -> (wordPar : Parikh n)
  -> (wordParikh cmap w ≡ wordPar)
  -> (langParikh : SemiLinSet n)
  -> (langParikh ≡ reSemiLin cmap r )
  -> (InSemiLin wordPar langParikh ) 
reParikhCorrect cmap .RETypes.ε .[] RETypes.EmptyMatch wordPar wpf langParikh lpf = 
  let
    emptyWordPar : wordPar ≡ v0
    emptyWordPar = trans (sym wpf) refl
    emptyLangPf : (( v0 , 0 , [] ) ∷ []) ≡ langParikh
    emptyLangPf = sym lpf
    zeroSelf : v0 +v v0 ≡ v0
    zeroSelf = v0identLeft
    inSemi : InSemiLin wordPar (( v0 , 0 , [] ) ∷ [] )
    inSemi = InHead wordPar (v0 , zero , []) [] (v0 , trans zeroSelf (sym emptyWordPar))
  in subst (λ x → InSemiLin wordPar x) emptyLangPf inSemi
reParikhCorrect cmap .(RETypes.Lit c) .(c ∷ []) (RETypes.LitMatch c) wordPar wpf langParikh lpf =
  let
    basisPf : wordPar ≡ (basis (cmap c))
    basisPf = trans (sym wpf) (trans refl v0identRight)
    basisSemiPf : langParikh ≡ Data.List.[ (basis (cmap c)) , 0 , []  ]
    basisSemiPf = lpf
    inSemi : InSemiLin wordPar (( (basis (cmap c)) , 0 , [] ) ∷ [] )
    inSemi = InHead wordPar (basis (cmap c) , 0 , []) [] (v0 , sym (trans basisPf (sym v0identRight)))
  in subst (λ x → InSemiLin wordPar x) (sym basisSemiPf) inSemi
reParikhCorrect cmap (r1 RETypes.+ .r2) w (RETypes.LeftPlusMatch r2 match) wordPar wpf langParikh lpf =
  let
    leftParikh = reSemiLin cmap r1
    leftInSemi = reParikhCorrect cmap r1 w match wordPar wpf leftParikh refl
    --Idea: show that langParikh is leftParikh ++ rightParikh
    --And that this means that it must be in the concatentation
  in {! !}
reParikhCorrect cmap ._ s (RETypes.RightPlusMatch r1 match) wordPar wpf langParikh lpf = {!!}
reParikhCorrect cmap ._ ._ (RETypes.ConcatMatch match match₁) wordPar wpf langParikh lpf = {!!}
reParikhCorrect cmap ._ .[] RETypes.EmptyStarMatch wordPar wpf langParikh lpf = {!!}
reParikhCorrect cmap ._ ._ (RETypes.StarMatch match match₁) wordPar wpf langParikh lpf = {!!}


reParikhComplete : {n : ℕ} -> {null? : RETypes.Null?}
  -> (cmap : Char -> Fin.Fin n)
  -> (r : RETypes.RE null?)
  -> (v : Parikh n )
  -> (InSemiLin v (reSemiLin cmap r ) )
  -> ∃ (λ w -> (v ≡ wordParikh cmap w) × (RETypes.REMatch w r) ) 
reParikhComplete cmap r v linComb = {!!}
