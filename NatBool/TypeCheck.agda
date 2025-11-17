module NatBool.TypeCheck where

open import NatBool.Language

open import Relation.Nullary using (Dec; yes; no; ¬_)

type-check : ∀ (t : Term) (T : Type) → Dec (⊢ t ⦂ T)
type-check `true         Nat  = no λ ()
type-check `true         Bool = yes ⊢true
type-check `false        Nat  = no λ ()
type-check `false        Bool = yes ⊢false
type-check (`if c th el) T
  with type-check c Bool | type-check th T | type-check el T
... | no c-not-bool | _           | _           = no bad-condition
  where
  bad-condition : ¬ (⊢ (`if c th el) ⦂ T)
  bad-condition (⊢if c-bool _ _) = c-not-bool c-bool

... | yes _         | no th-not-T | _           = no bad-then
  where
  bad-then : ¬ (⊢ `if c th el ⦂ T)
  bad-then (⊢if _ th-T _) = th-not-T th-T

... | yes _         | yes _       | no el-not-T = no bad-else
  where
  bad-else : ¬ (⊢ `if c th el ⦂ T)
  bad-else (⊢if _ _ el-T) = el-not-T el-T

... | yes c-bool    | yes th-T    | yes el-T    =
  yes (⊢if c-bool th-T el-T)

type-check `zero         Nat  = yes ⊢zero
type-check `zero         Bool = no λ ()
type-check (`suc n)      Nat with type-check n Nat
... | yes n-nat     = yes (⊢suc n-nat)
... | no  n-not-nat = no bad-n-suc
  where
  bad-n-suc : ¬ (⊢ `suc n ⦂ Nat)
  bad-n-suc (⊢suc n-nat) = n-not-nat n-nat
type-check (`suc n)      Bool = no λ ()
type-check (`zero? n)    Nat  = no λ ()
type-check (`zero? n)    Bool with type-check n Nat
... | yes n-nat     = yes (⊢zero? n-nat)
... | no  n-not-nat = no bad-n-zero?
  where
  bad-n-zero? : ¬ (⊢ `zero? n ⦂ Bool)
  bad-n-zero? (⊢zero? n-nat) = n-not-nat n-nat
