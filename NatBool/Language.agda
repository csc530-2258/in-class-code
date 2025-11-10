module NatBool.Language where

data Term : Set where
  `true  : Term
  `false : Term
  `if    : Term → Term → Term → Term
  `zero  : Term
  `suc   : Term → Term
  `zero? : Term → Term

data BoolValue : Term → Set where
  BV-true  : BoolValue `true
  BV-false : BoolValue `false

data NatValue : Term → Set where
  NV-zero : NatValue `zero
  NV-suc  : ∀ {t : Term} → NatValue t → NatValue (`suc t)

data Value : Term → Set where
  V-bool : ∀ {t : Term} → BoolValue t → Value t
  V-nat  : ∀ {t : Term} → NatValue  t → Value t

-- —→ : \em\to
infix 4 _—→_
data _—→_ : Term → Term → Set where
  if-true      : ∀ {th el} → `if `true  th el —→ th
  if-false     : ∀ {th el} → `if `false th el —→ el
  reduce-if    : ∀ {c c′ th el} →
                 c —→ c′ →
                 `if c th el —→ `if c′ th el
  reduce-suc   : ∀ {n n′} →
                 n —→ n′ →
                 `suc n —→ `suc n′
  zero?-zero   : `zero? `zero —→ `true
  zero?-suc    : ∀ {n} →
                 NatValue n →
                 `zero? (`suc n) —→ `false
  reduce-zero? : ∀ {n n′} →
                 n —→ n′ →
                 `zero? n —→ `zero? n′

infix 2 _—→*_
data _—→*_ : Term → Term → Set where
  no-steps    : ∀ {t} → t —→* t
  multi-steps : ∀ {t t₁ t₂} →
                t —→ t₁ → t₁ —→* t₂ →
                t —→* t₂
