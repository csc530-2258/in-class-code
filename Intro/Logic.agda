module Intro.Logic where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

-- Some unicode:
-- ₁ : \_1
-- ₂ : \_2
-- × : \times  or  \x
-- ⊎ : \u+
-- ⊥ : \bot
-- ¬ : \neg
-- Σ : \GS  or  \Sigma
-- ∃ : \ex  or \exists
-- ′ : \' (this isn't super necessary, but technically I'm using the
--         unicode character for "prime")

-- It's our and!
infixr 2 _×_
infixr 4 _,_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_


-- It's our or!
infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B


-- False!
data ⊥ : Set where
-- this space intentionally left blank


-- From false, everything follows
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()


-- Negation!
infix 3 ¬_
¬_ : Set → Set
¬ A = A → ⊥


-- Slightly more readable than ⊥-elim!
contradiction : ∀ {A B : Set} → A → ¬ A → B
contradiction a not-a = ⊥-elim (not-a a)


-- Existence with explict type!
record Σ (A : Set) (P : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : P proj₁
open Σ


-- Existence with implicit type!
∃ : ∀ {A : Set} (P : A → Set) → Set
∃ {A} P = Σ A P


-- Syntax declarations for human eyes
infix 2 ∃ Σ
syntax ∃ (λ x → P) = ∃[ x ] P
syntax Σ A (λ x → P) = Σ[ x ∈ A ] P


-- EXAMPLES
my-nat-pair : ℕ × ℕ
my-nat-pair = 5 , 7

proj₁-works : proj₁ my-nat-pair ≡ 5
proj₁-works = refl

my-nat-triple : ℕ × ℕ × ℕ
my-nat-triple = 1 , 2 , 3

prop1 : ∀ {A B C : Set} → ((A × B) → C) → (A → (B → C))
prop1 hyp a b = hyp (a , b)

prop2 : ∀ {A B C : Set} → (A → (B → C)) → ((A × B) → C)
prop2 hyp ab = hyp (proj₁ ab) (proj₂ ab)

prop2′ : ∀ {A B C : Set} → (A → (B → C)) → ((A × B) → C)
prop2′ hyp (a , b) = hyp a b

prop3 : ∀ {A B C : Set} →
        (A × (B ⊎ C)) → ((A × B) ⊎ (A × C))
prop3 (a , inj₁ b) = inj₁ (a , b)
prop3 (a , inj₂ c) = inj₂ (a , c)

prop4 : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
prop4 a2b not-b a = not-b (a2b a)

prop5 : ∀ {A B : Set} → ¬ (A ⊎ B) → (A → B)
prop5 hyp a = ⊥-elim (hyp (inj₁ a))

prop5′ : ∀ {A B C : Set} → ¬ (A ⊎ B) → (A → C)
prop5′ hyp a = contradiction (inj₁ a) hyp

prop6 : ∀ {A B C : Set} → (A → (B ⊎ C)) → ¬ B → ¬ C → ¬ A
prop6 hyp not-b not-c a with hyp a
prop6 hyp not-b not-c a | inj₁ b = not-b b
prop6 hyp not-b not-c a | inj₂ c = not-c c

prop6′ : ∀ {A B C : Set} → (A → (B ⊎ C)) → ¬ B → ¬ C → ¬ A
prop6′ hyp not-b not-c a with hyp a
... | inj₁ b = not-b b
... | inj₂ c = not-c c

prop7 : Σ ℕ (λ x → x ≡ 4)
prop7 = 4 , refl

prop7′ : Σ[ x ∈ ℕ ] x ≡ 4
prop7′ = 4 , refl

prop7′′ : ∃[ x ] x ≡ 4
prop7′′ = 4 , refl

prop8 : ∀ {A : Set} {P Q : A → Set} →
        ∃[ x ] (P x) × (Q x) →
        (∃[ x ] P x) × (∃[ x ] Q x)
prop8 (a , pa , qa) = (a , pa) , (a , qa)
