module NatBool.Properties where

open import NatBool.Language

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)

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


bool-vals : ∀ {t} → Value t → ⊢ t ⦂ Bool → BoolValue t
bool-vals (V-bool t-bv) t-bool = t-bv
bool-vals (V-nat NV-zero) ()
bool-vals (V-nat (NV-suc x)) ()


nat-vals : ∀ {t} → Value t → ⊢ t ⦂ Nat → NatValue t
nat-vals (V-bool BV-true) ()
nat-vals (V-bool BV-false) ()
nat-vals (V-nat t-nv) t-nat = t-nv


data Progress (t : Term) : Set where
  done : Value t → Progress t
  step : ∀ {t′} → t —→ t′ → Progress t


-- ∀ {t T} → ⊢ t ⦂ T → Value t ⊎ ∃[ t′ ] t —→ t′
progress : ∀ {t T} → ⊢ t ⦂ T → Progress t
progress ⊢true  = done (V-bool BV-true)
progress ⊢false = done (V-bool BV-false)
progress ⊢zero  = done (V-nat NV-zero)
progress (⊢suc n-nat) with progress n-nat
... | step n-step = step (reduce-suc n-step)
... | done n-val  = done (V-nat (NV-suc (nat-vals n-val n-nat)))
progress (⊢if c-bool _ _) with progress c-bool
... | step c-step = step (reduce-if c-step)
... | done c-val with bool-vals c-val c-bool
...   | BV-true  = step if-true
...   | BV-false = step if-false
progress (⊢zero? n-nat) with progress n-nat
... | step n-step = step (reduce-zero? n-step)
... | done n-val with nat-vals n-val n-nat
...   | NV-zero      = step zero?-zero
...   | NV-suc pn-nv = step (zero?-suc pn-nv)


preserve : ∀ {t t′ T} → ⊢ t ⦂ T → t —→ t′ → ⊢ t′ ⦂ T
preserve (⊢if _ th-T _)         if-true  = th-T
preserve (⊢if _ _ el-T)         if-false = el-T
preserve (⊢if c-bool th-T el-T) (reduce-if c-step) =
  ⊢if (preserve c-bool c-step) th-T el-T
preserve (⊢suc n-nat)           (reduce-suc n-step) =
  ⊢suc (preserve n-nat n-step)
preserve (⊢zero? _)     zero?-zero            = ⊢true
preserve (⊢zero? _)     (zero?-suc _)         = ⊢false
preserve (⊢zero? n-nat) (reduce-zero? n-step) =
  ⊢zero? (preserve n-nat n-step)


unstuck : ∀ {t T} → ⊢ t ⦂ T → ¬ (Stuck t)
unstuck t-T (t-normal , t-not-value) with progress t-T
... | done t-value = t-not-value t-value
... | step t-step  = t-normal t-step


preserves : ∀ {t t′ T} → ⊢ t ⦂ T → t —→* t′ → ⊢ t′ ⦂ T
preserves t-T no-steps = t-T
preserves t-T (multi-steps fst-step rst-steps) =
  preserves (preserve t-T fst-step) rst-steps


wttdgs : ∀ {t t′ T} → ⊢ t ⦂ T → t —→* t′ → ¬ (Stuck t′)
wttdgs t-T t-steps = unstuck (preserves t-T t-steps)


data Finished (t : Term) : Set where
  ran       : Value t → Finished t
  timed-out : Finished t


data Steps (t : Term) : Set where
  steps : ∀ {t′ : Term} → t —→* t′ → Finished t′ → Steps t


eval : ∀ {t T} → ℕ → ⊢ t ⦂ T → Steps t
eval zero    _   = steps no-steps timed-out
eval (suc n) t-T with progress t-T
... | done t-value = steps no-steps (ran t-value)
... | step t-step  with eval n (preserve t-T t-step)
...   | steps rst-steps fin =
  steps (multi-steps t-step rst-steps) fin
