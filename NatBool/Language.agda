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
