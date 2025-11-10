module NatBool.Properties where

open import NatBool.Language

open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)

Normal : Term → Set
Normal t = ∀ {t′} → ¬ (t —→ t′)

Stuck : Term → Set
Stuck t = (Normal t) × ¬ (Value t)

values-are-normal : ∀ {t} → Value t → Normal t
values-are-normal (V-bool BV-true)  ()
values-are-normal (V-bool BV-false) ()
values-are-normal (V-nat  NV-zero)  ()
values-are-normal (V-nat (NV-suc n-val)) (reduce-suc n-step) =
  values-are-normal (V-nat n-val) n-step

-- det : ∀ {t t₁ t₂} → t —→ t₁ → t —→ t₂ → t₁ ≡ t₂
-- det if-true  if-true = refl
-- det if-false t-step2 = {!   !}
-- det {`if c th el} (reduce-if c-step1) (reduce-if c-step2) =
--   cong (λ v → `if v th el) (det c-step1 c-step2)
-- det (reduce-suc t-step1) t-step2 = {!   !}
-- det zero?-zero t-step2 = {!   !}
-- det (zero?-suc x) t-step2 = {!   !}
-- det (reduce-zero? t-step1) t-step2 = {!   !}
