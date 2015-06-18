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

open import Data.List.NonEmpty

--open List-solver renaming (nil to :[]; _⊕_ to _:++_; _⊜_ to _:≡_; solve to listSolve; prove to listProve)

open import Algebra
import Algebra.FunctionProperties as FunProp

open import Data.Maybe

open import Data.Nat



open import RETypes


import Relation.Binary.Reflection as Ref

import Data.Bool.Properties







listDivisions : List Char -> List (List Char × List Char)
listDivisions [] = ( [] , []) ∷ []
listDivisions (h ∷ t) = ([] , h ∷ t ) ∷ (Data.List.map (λ p -> ( (h ∷ proj₁ p) , proj₂ p )) (listDivisions t) ) 
  
elementMatches : {A : Set} (f : A -> Bool) -> List A -> Bool
elementMatches f [] = false
elementMatches f (h ∷ t) = (f h) ∨ elementMatches f t

{-
mutual

  starMatch : {n : Null?} -> (RE n) -> List Char -> List Char -> (List Char -> Bool) -> Bool
  starMatch (r *) s1 (sh ∷ st) k =  (acc r (s1 ++ Data.List.[ sh ]) null ∧ acc ( r *) st k )  ∨ starMatch (r *) (s1 ++ Data.List.[ sh ]) st k
  starMatch (r *) s1 [] k = false
  starMatch _ _ _ _ = false
-}

{-# TERMINATING #-}
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
  in k cs ∨ acc r cs (\cs' -> acc (r *) cs' k)
  --acc r cs (\cs' -> acc (r) cs' k)
  --acc (r *) (sFirst ∷ sRest) k =  starMatch r (sFirst ∷ [] ) sRest k

accept : {n : Null?} -> RE n -> List Char -> Bool
accept r s = acc r s null

concatPreservesNonNull : {s1 : List Char}
  -> {s2 : List Char}
  -> (∃ λ (h : Char) -> ∃ λ (t : List Char) -> (s1 ≡ h ∷ t) )
  -> (∃ λ (h : Char) -> ∃ λ (t : List Char) -> (s1 ++ s2 ≡ h ∷ t) )
concatPreservesNonNull {s1} {s2 = []} (sh , st , pf) =
  let
    concatPf : s1 ++ [] ≡ s1
    concatPf = (solve (suc zero) (λ x → x ⊕ nil , x) (λ {x} → refl)) s1 --Should be easy, I might have already proved something similar,
    --This is probably a good place to try the List prover stuff
  in sh , st , trans concatPf pf
  where open List-solver
concatPreservesNonNull {s1} {s2 = x ∷ s2} (sh , st , pf) = 
  let
    --subProof : (∃ λ (h : Char) -> ∃ λ (t : List Char) -> (s1 ++ s2 ≡ h ∷ t) )
    (h , t , subProof) = concatPreservesNonNull {s1} {s2} (sh , st , pf)
    p2 : ((sh ∷ st) ++ s2 ≡ h ∷ t)
    p2 = subst (λ x₁ → x₁ ++ s2 ≡ h ∷ t) pf subProof 
  in sh , (st ++ (x ∷ s2)) , cong (λ x₁ → x₁ ++ x ∷ s2) pf
 

concatPreservesNonNull2 : {s1 : List Char}
  -> {s2 : List Char}
  -> (∃ λ (h : Char) -> ∃ λ (t : List Char) -> (s2 ≡ h ∷ t) )
  -> (∃ λ (h : Char) -> ∃ λ (t : List Char) -> (s1 ++ s2 ≡ h ∷ t) )
concatPreservesNonNull2 {[]} (sh , st , pf) = sh , st , pf
concatPreservesNonNull2 {x ∷ s1} {s2} (sh , st , pf) = x , s1 ++ s2 , refl


open ≡-Reasoning

nullCorrect : (r : RE NonNull) -> (s : List Char ) -> (REMatch s r) 
  -> (∃ λ (h : Char) -> ∃ λ (t : List Char) -> (s ≡ h ∷ t) )
nullCorrect .(Lit c) .(c ∷ []) (LitMatch c) = c , [] , refl
nullCorrect ._ s (LeftPlusMatch {nb = BothNullB} {r1 = r1} r2 match) = nullCorrect r1 s match
nullCorrect ._ s (RightPlusMatch {nb = BothNullB} r1 {r2 = r2} match) = nullCorrect r2 s match
nullCorrect .(r1 · r2) s (ConcatMatch {nt = LeftNullT} {s1 = s1} {s2 = s2} {spf = spf} {r1 = r1} {r2 = r2}  match1 match2) = 
  let
    sh , st , subPf = concatPreservesNonNull2 {s1 = s1} {s2 = s2} (nullCorrect r2 s2 match2)
  in sh , st , trans (sym spf) subPf   --subH , subT , ? 
nullCorrect ._ s (ConcatMatch {nt = BothNonNullT} {s1 = s1} {s2 = s2} {spf = spf} {r1 = r1} {r2 = r2} match1 match2) =   
  let
    sh , st , subPf = concatPreservesNonNull2 {s1 = s1} {s2 = s2} (nullCorrect r2 s2 match2)
  in sh , st , trans (sym spf) subPf 
nullCorrect ._ s (ConcatMatch {nt = RightNullT} {s1 = s1} {s2 = s2} {spf = spf} {r1 = r1} {r2 = r2} match1 match2) = 
  let
    sh , st , subPf = concatPreservesNonNull {s1 = s1} {s2 = s2} (nullCorrect r1 s1 match1)
  in sh , st , trans (sym spf) subPf  -- concatPreservesNonNull (nullCorrect r1 s1 match1)

--Taken from http://gelisam.blogspot.ca/2010/10/equality-is-useless-transmutation.html
--Can probably be done with more complicated existing stuff, but this is easier
mySubst : {X : Set} 
       → (P : X → Set) 
       → (x y : X) 
       → x ≡ y 
       → P x 
       → P y 
mySubst P v .v refl p = p 


orLemma1 : {x : Bool} {y : Bool} -> (y ≡ true) -> (y ∨ x) ≡ true
orLemma1 {x} {true} pf = refl
orLemma1 {x} {false} ()

andElim1 : {x : Bool} {y : Bool} -> (x ∧ y) ≡ true -> (x ≡ true)
andElim1 {true} pf = refl
andElim1 {false} ()

--TODO Pattern match on and first
andElim2 : {x : Bool} {y : Bool} -> (x ∧ y) ≡ true -> (y ≡ true)
andElim2 {y = true} pf = refl
andElim2 {true} {false} ()
andElim2 {false} {false} ()

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

listRightIdent : { x : List Char} -> (x ++ []) ≡ x
listRightIdent {[]} = refl
listRightIdent {x ∷ x₁} = cong (_∷_ x) (listRightIdent {x₁})

listAssoc : {x y z : List Char} -> (x ++ y) ++ z ≡ x ++ (y ++ z)
listAssoc {[]} = λ {y} {z} → refl
listAssoc {xh ∷ xt} {y} {z} = cong (_∷_ xh) (listAssoc {xt} {y} {z})

maybeHead : List Char -> Maybe Char
maybeHead [] = nothing
maybeHead (x ∷ _) = just x

fakeTail : List Char -> List Char
fakeTail [] = []
fakeTail (_ ∷ t) = t 

myFromJust : Maybe Char -> Char
myFromJust (just x) = x
myFromJust (nothing) = 'a'

sameHead : {a : Char}{b : Char}{l1 : List Char}{l2 : List Char} -> ((a ∷ l1) ≡ (b ∷ l2)) -> (a ≡ b)
sameHead {a} {b} {l1} {l2} pf = 
  let
    maybeSameHead : (just a) ≡ (just b)
    maybeSameHead = cong (maybeHead) pf
  in cong myFromJust maybeSameHead

sameTail : {a : Char}{b : Char}{l1 : List Char}{l2 : List Char} -> ((a ∷ l1) ≡ (b ∷ l2)) -> (l1 ≡ l2)
sameTail {a} {b} {l1} {l2} pf = cong fakeTail pf

emptyMiddleList : {c : Char}{s1 s2 : List Char} -> (c ∷ s1 ≡ (c ∷ []) ++ s2 ) -> s1 ≡ s2
emptyMiddleList {c} {s1} {s2} spf = 

  let
    p0 : (s1 ≡ [] ++ s2 )
    p0 = cong fakeTail spf
    p1 : [] ++ s2 ≡ s2
    p1 = refl
  in trans p0 p1

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
accCorrect (Lit .c) (c1 ∷ srest ) (.c ∷ []) s2 k stringProof (LitMatch c) kproof with (c Data.Char.≟ c1)
... | yes eqPf =   let
    sameHeads : c ≡ c1
    sameHeads = sameHead stringProof
    p0 : c Data.List.∷ srest ≡ c1 Data.List.∷ srest
    p0 = cong (λ x → x ∷ srest) sameHeads

    flipProof : (c1 ∷ srest ) ≡ (c ∷ []) ++ s2
    flipProof = sym stringProof
    cFlip : (c ∷ srest ) ≡ (c ∷ []) ++ s2
    cFlip = trans p0 flipProof
    restProof : srest ≡ s2
    restProof = emptyMiddleList cFlip

    primEq : (Dec (c ≡ c1))
    primEq = yes sameHeads
    
    pf3 = cong (λ theChar -> acc (Lit c) (c ∷ srest) k ) sameHeads
    
    
    
  in trans (cong k restProof) kproof
accCorrect (Lit .c) (c1 ∷ srest ) (.c ∷ []) s2 k stringProof (LitMatch c) () | no pf

{-
  let
    sameHeads = sameHead stringProof
    primEq : (Dec (c ≡ c1))
    primEq = yes sameHeads
    pf3 = cong (λ theChar -> acc (Lit c) (c ∷ srest) k ) sameHeads
    restProof : srest ≡ s2
    restProof = {!!}
  in cong k restProof
-}
accCorrect (.r1 · .r2 ) s .s1 s2  k  split1 (ConcatMatch {_} {_} {n3} {nt} {s1'} {s2'} {s1} {spf'} {r1} {r2} subMatch1 subMatch2) kproof  = 
  let
           --s1 = s1' ++ s2'
           split2 : (s1' ++ s2') ≡ s1 
           split2 = spf' --refl
           split3 : (s1' ++ s2') ++ s2 ≡ s1 ++ s2
           split3 = cong (λ x -> x ++ s2) split2
           split4 : s1' ++ s2' ++ s2 ≡ (s1' ++ s2') ++ s2 
           split4 =  sym (listAssoc {s1'} {s2'} {s2})
           transChain : s1' ++ s2' ++ s2 ≡ s
           transChain = trans split4 (trans split3 split1)
  in accCorrect r1 s s1' (s2' ++ s2) (\cs -> acc r2 cs k) transChain
    subMatch1 (accCorrect r2 (s2' ++ s2) s2' s2 k refl subMatch2 kproof)
accCorrect (.r1 + .r2 ) s .s1 s2  k  
  splitProof (LeftPlusMatch {_} {_} {n3} {nb} {s1} {r1} (r2) subMatch) kproof  = 
   orLemma1 (accCorrect r1 s s1 s2 k splitProof subMatch kproof )
accCorrect (.r1 + .r2) s .s1 s2  k  
  splitProof (RightPlusMatch {_} {_} {n3} {nb} {s1} (r1) {r2} subMatch) kproof  =
    let subCorrect = accCorrect r2 s s1 s2 k splitProof subMatch kproof
    in orLemma2 {acc r1 s k} {acc r2 s k} subCorrect
accCorrect (.r *) [] ._ [] k _ (EmptyStarMatch {r}) kproof = kproof

accCorrect {MaybeNull} (.r *) (sh ∷ st ) .s1 s2  k  split1 (StarMatch {c1} {s1t'} {s2'} {s1} {spf} {r} subMatch1 subMatch2) kproof  = 
  let
           s = (sh ∷ st )
           s1' = (c1 ∷ s1t')
           
           split2 : (s1' ++ s2') ≡ s1 
           split2 = spf
           split3 : (s1' ++ s2') ++ s2 ≡ s1 ++ s2
           split3 = cong (λ x -> x ++ s2) split2
           split4 : s1' ++ s2' ++ s2 ≡ (s1' ++ s2') ++ s2 
           split4 =  sym (listAssoc {s1'} {s2'} {s2})
           transChain : s1' ++ s2' ++ s2 ≡ s
           transChain = trans split4 (trans split3 split1)
           sub2' : REMatch {MaybeNull} s2' (r *) 
           sub2' = subMatch2
           subCorrect : acc (r *) (s2' ++ s2) k ≡ true
           subCorrect = accCorrect (r *) (s2' ++ s2) s2' s2 k refl subMatch2 kproof
           rightCorrect : acc r s (\cs' -> acc (r *) cs' k) ≡ true
           rightCorrect = accCorrect r s s1' (s2' ++ s2) (λ cs → acc (r *) cs k) transChain subMatch1 subCorrect
           orCorrect : (k s ∨ acc r s (\cs' -> acc (r *) cs' k) ) ≡ true
           orCorrect = orLemma2 {x = k s} rightCorrect
  --TODO pass in x and y explicitly
  in orCorrect --accCorrect r s s1' (s2' ++ s2) (\cs -> acc (r *) cs k) transChain
    --subMatch1 (accCorrect (r *) (s2' ++ s2) s2' s2 k refl subMatch2 kproof)

accCorrect (r *) (sh ∷ st) [] s2 k sp1 _ kproof = 
  let
    s = sh ∷ st
    sp2 : s2 ≡ s
    sp2 = sp1
    kproof2 : k s ≡ k s2
    kproof2 = cong k (sym sp1)
    kproof3 : k s ≡ true
    kproof3 = trans kproof2 kproof
    --orProof : (k s ∨ starMatch r [] s k) ≡ true
    orProof = orLemma1 kproof3
  in orProof
 --accCorrect r s s1' (s2' ++ s2) (\cs -> acc (r *) cs k) transChain
    --subMatch1 (accCorrect (r *) (s2' ++ s2) s2' s2 k refl subMatch2 kproof)
--accCorrect  (.r *) s ._ s2 k sp1 (StarMatch {s1'} {s1''} {r} sub1 sub2) kproof = ?
accCorrect ∅ _ _ _ _ _ ()
accCorrect ε (_ ∷ _ ) _ _ _ () _
accCorrect _ [] (_ ∷ _ ) _ _ () _ _
accCorrect _ [] _ (_ ∷ _ ) _ () _ _
accCorrect (Lit _) [] _ _ _ () _ _
accCorrect {._} (_* _) [] [] [] _ _
             (StarMatch {_} {_} {_} {._} {()} {._} _ _) _ 
--accCorrect _ _ _ _ _ _ _ _ = {!!} --This case should disappear when I finish star



boolExclMiddle : {x : Bool} { y : Bool } -> (x ∨ y ≡ true ) -> (x ≡ false) -> (y ≡ true)
boolExclMiddle {true} p1 () 
boolExclMiddle {false} p1 p2 = p1


{-# TERMINATING #-}
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
accComplete (_·_ {n1} {n2} r1  r2) s k pf = 
  let
    sub1 : acc r1 s (λ s' -> acc r2 s' k) ≡ true
    sub1 = pf
    s11 , s2' , psub1 , psub2 , match1  = accComplete r1 s (λ s' -> acc r2 s' k) pf
    s12 , s2 , p1 , p2 , match2 = accComplete r2 s2' k psub2
    localAssoc :  s11 ++ (s12 ++ s2) ≡ (s11 ++ s12) ++ s2
    localAssoc = sym (listAssoc {s11} {s12} {s2})
    subProof1 : s11 ++ s2' ≡ s11 ++ (s12 ++ s2)
    subProof1 = sym ( cong (λ x -> s11 ++ x) p1 )
    subProof2 : s11 ++ s2' ≡ (s11 ++ s12) ++ s2 
    subProof2 = trans subProof1 localAssoc
    stringProof = trans (sym subProof2) psub1
  in (s11 ++ s12 ) , s2 , stringProof , p2 , (ConcatMatch {spf = refl} match1 match2)
  
accComplete (r1 + r2) s k accProof with (orCases accProof)
...  | inj₁ leftTrue  = 
  let
    s1 , s2 , p1 , p2 , match = accComplete r1 s k leftTrue
  in s1 , s2 , p1 , p2 , LeftPlusMatch r2 match
...  | inj₂ rightTrue  = let
    s1 , s2 , p1 , p2 , match = accComplete r2 s k rightTrue
  in s1 , s2 , p1 , p2 , RightPlusMatch r1 match
accComplete (r *) [] k pf =  [] , [] , refl , pf , EmptyStarMatch
accComplete {MaybeNull} (r *) (sh ∷ st) k accProof with (orCases accProof)
... | inj₁ leftTrue  =  [] , (sh ∷ st) , refl , leftTrue , EmptyStarMatch
... | inj₂ rightTrue  =  
  let
    rTest : RE NonNull
    rTest = r
    s = sh ∷ st
    sub1 : acc r s (λ s' -> acc (r *) s' k) ≡ true
    sub1 = rightTrue
    s11 , s2' , psub1 , psub2 , match1  = accComplete r s (λ s' -> acc (r *) s' k) rightTrue
    s12 , s2 , p1 , p2 , match2 = accComplete (r *) s2' k psub2
    localAssoc :  s11 ++ (s12 ++ s2) ≡ (s11 ++ s12) ++ s2
    localAssoc = sym (listAssoc {s11} {s12} {s2})
    subProof1 : s11 ++ s2' ≡ s11 ++ (s12 ++ s2)
    subProof1 = sym ( cong (λ x -> s11 ++ x) p1 )
    subProof2 : s11 ++ s2' ≡ (s11 ++ s12) ++ s2 
    subProof2 = trans subProof1 localAssoc
    stringProof = trans (sym subProof2) psub1

    s11h , s11t , nnpf = nullCorrect r s11 match1
    nonNullPf : s11 ≡ s11h ∷ s11t
    nonNullPf = nnpf


    m1 : REMatch (s11h ∷ s11t) r 
    m1 = mySubst (λ str → REMatch str r) s11 (s11h ∷ s11t) (nonNullPf) match1 
    m2 : REMatch s12 (r *)
    m2 = match2
    newSpf : (s11h ∷ s11t) ++ s2' ≡ s11 ++ s2'
    newSpf = {!!}
    --ourMatch : REMatch (s11 ++ s12) (r *)
    ourMatch = StarMatch {spf = newSpf} {r = rTest} m1 ? --m2
  in (s11 ++ s12 ) , s2 , stringProof , p2 , {!!} --ourMatch
accComplete ∅ _ _ ()
accComplete (Lit _) [] _ ()

acceptCorrect : 
  {n : Null? }
  (r : RE n) 
  (s : List Char) 
  -> (REMatch s r)
  -> (accept r s ≡ true )
acceptCorrect r s match = accCorrect r s s [] null listRightIdent match refl

nullEq : {x : List Char} -> (null x ≡ true ) -> (x ≡ [])
nullEq {[]} pf = refl
nullEq {x ∷ x₁} ()

substMatch : {n : Null?}{r : RE n}{s s1 : List Char} -> s1 ≡ s -> REMatch s1 r -> REMatch s r
substMatch refl m = m

acceptComplete :
  {n : Null? }
  (r : RE n) 
  (s : List Char) 
  -> (accept r s ≡ true )
  -> REMatch s r 
acceptComplete r s pf = 
  let
    s1 , s2 , sproof , ks2Proof , match = accComplete r s null pf
    s2Null : s2 ≡ []
    s2Null = nullEq ks2Proof
    sp3 : s1 ++ s2 ≡ s1 ++ [] 
    sp3 = cong (λ x -> s1 ++ x) s2Null
    sp4 : s1 ++ s2 ≡ s1
    sp4 = trans sp3 listRightIdent
    sp5 : s1 ≡ s
    sp5 = sym (trans (sym sproof) sp4)
  in substMatch sp5 match --match
