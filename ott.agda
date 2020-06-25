{-# OPTIONS --rewriting --prop #-}

module ott where 

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat hiding (_==_)
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
  A B C       : Set 
  P Q         : A → Set 
  x y z       : A
  f g h       : (x : A) → P x
  b b1 b2 b3  : Bool
  j k m n     : Nat
  xs ys zs    : List A

-- Declare some propositions

record ⊤ : Prop where constructor tt

data   ⊥ : Prop where

record _∧_ (X : Prop) (Y : Prop) : Prop where
  constructor _,_
  field
    fst : X
    snd : Y
open _∧_

-- Let's postulate the heterogenous OTT equality. 

infix 6 _==_

postulate
  _==_  : {A : Set}  {B : Set}  → A → B → Prop  -- term equality
  _===_ : Set → Set → Prop₁                     -- type equality
  
-- if A : Prop, and a b : A then a ≡ b 

HEq = _==_
syntax HEq {A = A} {B = B} x y = x ∈ A == y ∈ B


postulate
    _·_ : {A : Set} {B : Set} {C : Set} {a : A} {b : B} {c : C} 
          → (a ∈ A == b ∈ B) 
          → (b ∈ B == c ∈ C) 
          → (a ∈ A == c ∈ C) 

    sym : {A : Set} {B : Set} {a : A} {b : B}
          → (a ∈ A == b ∈ B) 
          → (b ∈ B == a ∈ A) 



-- Support for Booleans

postulate
  refl-Bool   : (Bool === Bool)

  refl-true   : (true  == true)  ≡ ⊤
  refl-false  : (false == false) ≡ ⊤
  conflict-tf : (true  == false) ≡ ⊥
  conflict-ft : (false == true)  ≡ ⊥

{-# REWRITE refl-true 
            refl-false
            conflict-tf 
            conflict-ft #-}

-- Support for dependent functions 

postulate
  -- We postulate that two codes for functions Πx:A.P(x) and Πy:B.Q(y)
  -- are equal when A == B and for all equal x and y, P(x) equals Q(y)
  -- 
  cong-Π : (B === A) → 
           ((x : A)(y : B) → y == x → P x === Q y)
           → 
           ((x : A) → P x) === ((y : B) → Q y)

  -- injectivity of pi-type constructor
  out-Π-1 : ((x : A) → P x) === ((y : B) → Q y) → (B === A)
  out-Π-2 : ((x : A) → P x) === ((y : B) → Q y) → ((x : A)(y : B) → y == x → P x === Q y)

-- Two functions f and g are equal when they are pointwise equal

  ext-λ : {A : Set} {B : Set}
    → {P : A → Set} {Q : B → Set}
    → (f : (x : A) → P x) (g : (y : B) → Q y)
    → ((x : A) (y : B) (x==y : x == y) → f x == g y)
    → (f == g)
    
infix 10 _[_⟩ _||_

postulate
  _[_⟩    : A → (A === B) → B      -- Coercion
  _||_    : (x : A) (Q : A === B)
          → x ∈ A == x [ Q ⟩ ∈ B   -- Coherence

postulate
  coerce-Bool : (pf : Bool === Bool)
              → b [ pf ⟩ ≡ b
  coerce-Π : 
      {A : Set} {B : Set}
      {P : A → Set} {Q : B → Set}
    → (E : ((x : A) → P x) === ((y : B) → Q y))
    → (f : (x : A) → P x) 
    → let B===A : B === A 
          B===A = out-Π-1 E 
          P===Q : (x : A)(y : B) → y == x → P x === Q y
          P===Q = out-Π-2 E 
          g : (y : B) → Q y 
          g = λ y → let x : A 
                        x = y [ B===A ⟩ 
                        v : P x 
                        v = f x
                        q : y == x
                        q = y || B===A 
                        R : P x === Q y 
                        R = P===Q x y q
                     in v [ R ⟩ 
      in 
      (f [ E ⟩ ≡ g)
  
{-# REWRITE coerce-Bool 
            coerce-Π
#-}

postulate 
  Quotient : (A : Set) → (R : A → A → Set) → Set 

  [_] : {A : Set} {R : A → A → Set} → A → Quotient A R 

  -- let [x] = v in k because pf 

  quotient-elim : {A : Set} 
                  {B : Set} 
                  {R : A → A → Set} 
                  → (v : Quotient A R)
                  → (k : (x : A) → B)
                  → (pf : ∀ (a a' : A) → R a a' → k a ∈ B == k a' ∈ B)
                  → B 

 -- let [x] = [v] in k(x) because pf ≡ k(v)
 
  quotient-reduce : {A : Set}
                    {B : Set}
                    {R : A → A → Set}
                    → (v : A)
                    → (k : A → B)
                    → (pf : ∀ (a a' : A) → R a a' → k a ∈ B == k a' ∈ B)
                    → quotient-elim [ v ] k pf ≡ k v 

  quotient-== : {A : Set}
                {R : A → A → Set}
                → (x y : A)
                → (R x y)
                → [ x ] ∈ Quotient A R == [ y ] ∈ Quotient A R
 
  quotient-=== : {A : Set} {R : A → A → Set}
                 {B : Set} {S : B → B → Set}
                 → (A === B)
                 → ((a a' : A) (b b' : B) → (a ∈ A == b ∈ B) → (a' ∈ A == b' ∈ B) → R a a' === S b b')
                 → Quotient A R === Quotient B S 

  out-quotient-1 : {A : Set} {R : A → A → Set} 
                   {B : Set} {S : B → B → Set} →
                   (Quotient A R === Quotient B S) → (A === B)

  out-quotient-2 : {A : Set} {R : A → A → Set} →
                   {B : Set} {S : B → B → Set} →
                   (Quotient A R === Quotient B S) → 
                   ((a a' : A) (b b' : B) → (a ∈ A == b ∈ B) → (a' ∈ A == b' ∈ B) → R a a' === S b b')

postulate 
  coerce-quotient : {A : Set} {R : A → A → Set} 
                    {B : Set} {S : B → B → Set} →
                    (v : Quotient A R) → 
                    (E : Quotient A R === Quotient B S) → 
                    v [ E ⟩ ≡ let A===B = out-quotient-1 E in 
                              quotient-elim v (λ a → [ a [ A===B ⟩ ]) 
                                (λ a a' aRa' → let b  = a  [ A===B ⟩ 
                                                   b' = a' [ A===B ⟩ 
                                                   a=b = a || A===B 
                                                   a'=b' = a' || A===B 
                                                   aRa'==bSb' = out-quotient-2 E a a' b b' a=b a'=b'
                                                   bSb' = aRa' [ aRa'==bSb' ⟩
                                                in 
                                                quotient-== b b' bSb')

{- REWRITE quotient-reduce  
           coerce-quotient -}
