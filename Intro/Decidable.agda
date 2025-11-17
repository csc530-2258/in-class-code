module Intro.Decidable where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)


data Bool : Set where
  true  : Bool
  false : Bool


_==_ : ℕ → ℕ → Bool
zero  == zero  = true
zero  == suc n = false
suc m == zero  = false
suc m == suc n = m == n


test1 : (2 == 4) ≡ false
test1 = refl

test2 : (5 == 5) ≡ true
test2 = refl


==→≡ : ∀ m n → (m == n) ≡ true → m ≡ n
==→≡ zero    zero    m==n = refl
==→≡ zero    (suc n) ()
==→≡ (suc m) zero    ()
==→≡ (suc m) (suc n) m==n = cong suc (==→≡ m n m==n)


≡→== : ∀ m n → m ≡ n → (m == n) ≡ true
≡→== zero    zero    m≡n  = refl
≡→== (suc m) (suc n) refl = ≡→== m n refl


data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A


suc-injective : ∀ {m n} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
suc-injective m-not-m refl = m-not-m refl


_≟_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero  ≟ zero  = yes refl
zero  ≟ suc n = no (λ ())
suc m ≟ zero  = no (λ ())
suc m ≟ suc n with m ≟ n
... | yes eq  = yes (cong suc eq)
... | no  neq = no (suc-injective neq)
