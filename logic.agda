module logic where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

-- ×: \times \x
-- ₁: \_1
-- ₂: \_2
infixr 2 _×_
infixr 4 _,_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_

-- EXAMPLES
my-nat-pair : ℕ × ℕ
my-nat-pair = 5 , 7

proj₁-works : proj₁ my-nat-pair ≡ 5
proj₁-works = refl

my-nat-triple : ℕ × ℕ × ℕ
my-nat-triple = 1 , 2 , 3

prop1 : ∀ {A B C : Set} → ((A × B) → C) → (A → (B → C))
prop1 hyp a b = hyp (a , b)
