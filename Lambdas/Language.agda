module Lambdas.Language where

open import Data.String using (String; _≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≢_)

Id = String

-- ⇒ : \=>
infixr 7 _⇒_
data Type : Set where
  Bool : Type
  Nat  : Type
  _⇒_  : Type → Type → Type


-- · : \cdot
infix  5 `λ_⦂_⇒_
infixl 7 _·_
data Term : Set where
  `true   : Term
  `false  : Term
  `zero   : Term
  `if     : Term → Term → Term → Term
  `zero?  : Term → Term
  `suc    : Term → Term
  `λ_⦂_⇒_ : Id → Type → Term → Term
  _·_     : Term → Term → Term
  `       : Id → Term


data BoolValue : Term → Set where
  BV-true  : BoolValue `true
  BV-false : BoolValue `false

data NatValue : Term → Set where
  NV-zero : NatValue `zero
  NV-suc  : ∀ {n} → NatValue n → NatValue (`suc n)

data LamValue : Term → Set where
  LV : ∀ {x : Id} {T : Type} {body : Term} →
       LamValue (`λ x ⦂ T ⇒ body)

data Value : Term → Set where
  V-bool : ∀ {t} → BoolValue t → Value t
  V-nat  : ∀ {t} → NatValue  t → Value t
  V-lam  : ∀ {t} → LamValue  t → Value t


infix 9 _[_:=_]
_[_:=_] : Term → Id → Term → Term
`true             [ y := V ] = `true
`false            [ y := V ] = `false
`zero             [ y := V ] = `zero
(`if c th el)     [ y := V ] = `if (c [ y := V ])
                                   (th [ y := V ])
                                   (el [ y := V ])
(`zero? n)        [ y := V ] = `zero? (n [ y := V ])
(`suc n)          [ y := V ] = `suc (n [ y := V ])
(func · arg)      [ y := V ] = (func [ y := V ]) · (arg [ y := V ])
(`λ x ⦂ T ⇒ body) [ y := V ] with x ≟ y
... | yes _ = `λ x ⦂ T ⇒ body
... | no  _ = `λ x ⦂ T ⇒ (body [ y := V ])
(` x)             [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x


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
  reduce-func  : ∀ {f f′ a} →
                 f —→ f′ →
                 (f · a) —→ (f′ · a)
  reduce-arg   : ∀ {f a a′} →
                 Value f → a —→ a′ →
                 (f · a) —→ (f · a′)
  -- This is sometimes called β-reduction
  subst        : ∀ {x : Id} {T : Type} {body arg : Term} →
                 Value arg →
                 (`λ x ⦂ T ⇒ body) · arg —→ body [ x := arg ]

infix 2 _—→*_
data _—→*_ : Term → Term → Set where
  no-steps    : ∀ {t} → t —→* t
  multi-steps : ∀ {t t₁ t₂} →
                t —→ t₁ → t₁ —→* t₂ →
                t —→* t₂

infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

begin_ : ∀ {t t′} → t —→* t′ → t —→* t′
begin steps = steps

_—→⟨_⟩_ : ∀ t {t′ t′′} → t —→ t′ → t′ —→* t′′ → t —→* t′′
t —→⟨ fst-step ⟩ rst-steps =
  multi-steps fst-step rst-steps

_∎ : ∀ t → t —→* t
t ∎ = no-steps


infixl 6 _,_⦂_
data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Type → Context


-- e.g., "x" ⦂ Nat ∈ Γ
infix 4 _⦂_∈_
data _⦂_∈_ : Id → Type → Context → Set where
  here  : ∀ {x T Γ} → x ⦂ T ∈ (Γ , x ⦂ T)
  there : ∀ {x y : Id} {A B : Type} {Γ : Context} →
          x ≢ y → x ⦂ A ∈ Γ →
          x ⦂ A ∈ (Γ , y ⦂ B)


infix 4 _⊢_⦂_
data _⊢_⦂_ : Context → Term → Type → Set where
  ⊢true  : ∀ {Γ} → Γ ⊢ `true ⦂ Bool
  ⊢false : ∀ {Γ} → Γ ⊢ `false ⦂ Bool
  ⊢if    : ∀ {Γ c th el A} →
           Γ ⊢ c ⦂ Bool → Γ ⊢ th ⦂ A → Γ ⊢ el ⦂ A →
           Γ ⊢ `if c th el ⦂ A
  ⊢zero  : ∀ {Γ} → Γ ⊢ `zero ⦂ Nat
  ⊢suc   : ∀ {Γ n} →
           Γ ⊢ n ⦂ Nat →
           Γ ⊢ `suc n ⦂ Nat
  ⊢zero? : ∀ {Γ n} →
           Γ ⊢ n ⦂ Nat →
           Γ ⊢ `zero? n ⦂ Bool
  ⊢lam   : ∀ {Γ x T b B} →
           Γ , x ⦂ T ⊢ b ⦂ B →
           Γ ⊢ (`λ x ⦂ T ⇒ b) ⦂ (T ⇒ B)
  ⊢app   : ∀ {Γ f a A B} →
           Γ ⊢ f ⦂ (A ⇒ B) → Γ ⊢ a ⦂ A →
           Γ ⊢ (f · a) ⦂ B
  ⊢var   : ∀ {Γ x T} →
           x ⦂ T ∈ Γ →
           Γ ⊢ ` x ⦂ T
