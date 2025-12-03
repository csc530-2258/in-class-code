module Lambdas.Properties where

open import Lambdas.Language

-- Benjamin Pierce: Types and Programming Languages
-- Benjamin Pierce: Software Foundations
-- Philip Wadler et al:
--        Programming Language Foundations in Agda

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.String using (_≟_)
open import Relation.Nullary
  using (¬_; yes; no; contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)

Normal : Term → Set
Normal t = ∀ {t′} → ¬ (t —→ t′)

Stuck : Term → Set
Stuck t = Normal t × ¬ (Value t)


nat-vals : ∀ {Γ t} → Value t → Γ ⊢ t ⦂ Nat → NatValue t
nat-vals (V-bool BV-true)  ()
nat-vals (V-bool BV-false) ()
nat-vals (V-nat  t-nv) t-nat = t-nv
nat-vals (V-lam LV) ()

bool-vals : ∀ {Γ t} →
            Value t → Γ ⊢ t ⦂ Bool → BoolValue t
bool-vals (V-bool t-bv) t-bool = t-bv
bool-vals (V-nat NV-zero)    ()
bool-vals (V-nat (NV-suc x)) ()
bool-vals (V-lam LV)         ()

lam-vals : ∀ {Γ t A B} →
           Value t → Γ ⊢ t ⦂ A ⇒ B → LamValue t
lam-vals (V-bool BV-true) ()
lam-vals (V-bool BV-false) ()
lam-vals (V-nat NV-zero) ()
lam-vals (V-nat (NV-suc x)) ()
lam-vals (V-lam t-lv) t-arrow = t-lv


data Progress (t : Term) : Set where
  done : Value t → Progress t
  step : ∀ {t′} → t —→ t′ → Progress t

progress : ∀ {t T} → ∅ ⊢ t ⦂ T → Progress t
progress ⊢true  = done (V-bool BV-true)
progress ⊢false = done (V-bool BV-false)
progress ⊢zero  = done (V-nat NV-zero)
progress (⊢suc n-nat) with progress n-nat
... | done n-val  = done (V-nat (NV-suc (nat-vals n-val n-nat)))
... | step n-step = step (reduce-suc n-step)
progress (⊢zero? n-nat) with progress n-nat
... | step n-step = step (reduce-zero? n-step)
... | done n-val with nat-vals n-val n-nat
...   | NV-zero = step zero?-zero
...   | NV-suc pn-nat = step (zero?-suc pn-nat)
progress (⊢if c-bool _ _) with progress c-bool
... | step c-step = step (reduce-if c-step)
... | done c-val with bool-vals c-val c-bool
...   | BV-true  = step if-true
...   | BV-false = step if-false
progress (⊢lam x) = done (V-lam LV)
progress (⊢app f-arrow a-A) with progress f-arrow
... | step f-step = step (reduce-func f-step)
... | done f-val with lam-vals f-val f-arrow | progress a-A
...   | LV | step a-step = step (reduce-arg f-val a-step)
...   | LV | done a-val  = step (subst a-val)


infix 3 _⊆_
_⊆_ : Context → Context → Set
Γ ⊆ Δ = ∀ {x A} → x ⦂ A ∈ Γ → x ⦂ A ∈ Δ

extend : ∀ {Γ Δ y B} → Γ ⊆ Δ → Γ , y ⦂ B ⊆ Δ , y ⦂ B
extend Γ⊆Δ here            = here
extend Γ⊆Δ (there neq x∈Γ) = there neq (Γ⊆Δ x∈Γ)

weaken : ∀ {Γ Δ t A} → Γ ⊆ Δ → Γ ⊢ t ⦂ A → Δ ⊢ t ⦂ A
weaken Γ⊆Δ ⊢true = ⊢true
weaken Γ⊆Δ ⊢false = ⊢false
weaken Γ⊆Δ ⊢zero = ⊢zero
weaken Γ⊆Δ (⊢if c-bool th-A el-A) =
  ⊢if (weaken Γ⊆Δ c-bool) (weaken Γ⊆Δ th-A) (weaken Γ⊆Δ el-A)
weaken Γ⊆Δ (⊢suc n-nat) = ⊢suc (weaken Γ⊆Δ n-nat)
weaken Γ⊆Δ (⊢zero? n-nat) = ⊢zero? (weaken Γ⊆Δ n-nat)
weaken Γ⊆Δ (⊢app f-arrow a-B) =
  ⊢app (weaken Γ⊆Δ f-arrow) (weaken Γ⊆Δ a-B)
weaken Γ⊆Δ (⊢lam b-B) = ⊢lam (weaken (extend Γ⊆Δ) b-B)
weaken Γ⊆Δ (⊢var x∈Γ) = ⊢var (Γ⊆Δ x∈Γ)


∅⊆Γ : ∀ {Γ} → ∅ ⊆ Γ
∅⊆Γ ()

drop : ∀ {Γ y A B} → Γ , y ⦂ A , y ⦂ B ⊆ Γ , y ⦂ B
drop here                      = here
drop (there neq here)          = contradiction refl neq
drop (there neq (there _ x∈Γ)) = there neq x∈Γ

swap : ∀ {Γ y z A B} →
       y ≢ z → Γ , z ⦂ B , y ⦂ A ⊆ Γ , y ⦂ A , z ⦂ B
swap y≢z here                        = there y≢z here
swap y≢z (there x≢y here)            = here
swap y≢z (there x≢y (there x≢z x∈Γ)) =
  there x≢z (there x≢y x∈Γ)


sub-pres : ∀ {Γ b y V A T} →
           Γ , y ⦂ A ⊢ b ⦂ T → ∅ ⊢ V ⦂ A →
           Γ ⊢ b [ y := V ] ⦂ T
sub-pres ⊢true  V-A = ⊢true
sub-pres ⊢false V-A = ⊢false
sub-pres ⊢zero  V-A = ⊢zero
sub-pres (⊢if c-bool th-T el-T) V-A =
  ⊢if (sub-pres c-bool V-A)
      (sub-pres th-T V-A)
      (sub-pres el-T V-A)
sub-pres (⊢suc n-nat) V-A = ⊢suc (sub-pres n-nat V-A)
sub-pres (⊢zero? n-nat) V-A = ⊢zero? (sub-pres n-nat V-A)
sub-pres (⊢app f-arrow a-C) V-A =
  ⊢app (sub-pres f-arrow V-A) (sub-pres a-C V-A)
sub-pres {y = y} (⊢var {x = x} here) V-A with x ≟ y
... | yes x-eq-y  = weaken ∅⊆Γ V-A
... | no  x-neq-y = contradiction refl x-neq-y
sub-pres {y = y} (⊢var {x = x} (there neq x∈Γ)) V-A
  with x ≟ y
... | yes x-eq-y  = contradiction x-eq-y neq
... | no  x-neq-y = ⊢var x∈Γ
sub-pres {y = y} (⊢lam {x = x} b-B) V-A with x ≟ y
... | yes refl    = ⊢lam (weaken drop b-B)
... | no  x-neq-y =
  ⊢lam (sub-pres (weaken (swap x-neq-y) b-B) V-A)

preserve : ∀ {t t′ T} → ∅ ⊢ t ⦂ T → t —→ t′ → ∅ ⊢ t′ ⦂ T
preserve (⊢if c-bool th-T el-T) if-true = th-T
preserve (⊢if c-bool th-T el-T) if-false = el-T
preserve (⊢if c-bool th-T el-T) (reduce-if c-step) =
  ⊢if (preserve c-bool c-step) th-T el-T
preserve (⊢suc n-nat) (reduce-suc n-step) =
  ⊢suc (preserve n-nat n-step)
preserve (⊢zero? n-nat) zero?-zero = ⊢true
preserve (⊢zero? n-nat) (zero?-suc n-nv) = ⊢false
preserve (⊢zero? n-nat) (reduce-zero? n-step) =
  ⊢zero? (preserve n-nat n-step)
preserve (⊢app f-arrow a-A) (reduce-func f-step) =
  ⊢app (preserve f-arrow f-step) a-A
preserve (⊢app f-arrow a-A) (reduce-arg f-val a-step) =
  ⊢app f-arrow (preserve a-A a-step)
preserve (⊢app (⊢lam b-T) a-A) (subst a-val) =
  sub-pres b-T a-A

unstuck : ∀ {t T} → ∅ ⊢ t ⦂ T → ¬ (Stuck t)
unstuck t-T (t-normal , t-not-value) with progress t-T
... | done t-value = t-not-value t-value
... | step t-step  = t-normal t-step


preserves : ∀ {t t′ T} → ∅ ⊢ t ⦂ T → t —→* t′ → ∅ ⊢ t′ ⦂ T
preserves t-T no-steps = t-T
preserves t-T (multi-steps fst-step rst-steps) =
  preserves (preserve t-T fst-step) rst-steps


wttdgs : ∀ {t t′ T} → ∅ ⊢ t ⦂ T → t —→* t′ → ¬ (Stuck t′)
wttdgs t-T t-steps = unstuck (preserves t-T t-steps)


data Finished (t : Term) : Set where
  ran       : Value t → Finished t
  timed-out : Finished t


data Steps (t : Term) : Set where
  steps : ∀ {t′ : Term} → t —→* t′ → Finished t′ → Steps t


eval : ∀ {t T} → ℕ → ∅ ⊢ t ⦂ T → Steps t
eval zero    _   = steps no-steps timed-out
eval (suc n) t-T with progress t-T
... | done t-value = steps no-steps (ran t-value)
... | step t-step  with eval n (preserve t-T t-step)
...   | steps rst-steps fin =
  steps (multi-steps t-step rst-steps) fin
