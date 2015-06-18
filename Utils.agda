module Utils where

open import Relation.Binary.PropositionalEquality

open import Data.List

listHeadEq : ∀ {α} {A : Set α} {x y : A} -> {xt yt : List A} -> x ∷ xt ≡ y ∷ yt -> x ≡ y
listHeadEq refl = refl

listTailEq : ∀ {α} {A : Set α} {x y : A} -> {xt yt : List A} -> x ∷ xt ≡ y ∷ yt -> xt ≡ yt
listTailEq refl = refl
