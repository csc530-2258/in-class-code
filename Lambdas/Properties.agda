module Lambdas.Properties where

open import Lambdas.Language

open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)

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


-- TODO: Finish this
sub-pres : ∀ {Γ b y V A T} →
           Γ , y ⦂ A ⊢ b ⦂ T → ∅ ⊢ V ⦂ A →
           Γ ⊢ b [ y := V ] ⦂ T
sub-pres = {!   !}

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
