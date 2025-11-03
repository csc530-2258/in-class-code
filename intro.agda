module intro where

-- Some unicode used below
-- ∀ : \all
-- → : \to
-- ℕ : \bN
-- ≡ : \==

id : ∀ {A : Set} → A → A
id a = a


prop2 : ∀ {A B C : Set} → (A → B) → (B → C) → (A → C)
prop2 a2b b2c a = b2c (a2b a)


data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}


infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero    + n = n
(suc m) + n = suc (m + n)


infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero    * n = 0
(suc m) * n = n + m * n


infix 4 _≡_
data _≡_ {A : Set} : A → A → Set where
    refl : ∀ {x : A} → x ≡ x


sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl


trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z


cong : ∀ {A B : Set} {x y : A} (f : A → B) →
       x ≡ y → f x ≡ f y
cong f refl = refl

infix  1 begin_
infixr 2 _≡⟨_⟩_
infix  3 _∎

begin_ : ∀ {A : Set} {x y : A} → x ≡ y → x ≡ y
begin eq = eq

-- ⟨: \<
-- ⟩: \>
_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} →
         x ≡ y → y ≡ z → x ≡ z
x ≡⟨ eq1 ⟩ eq2 = trans eq1 eq2

-- ∎: \qed
_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

-- In the standard library: +-identityˡ
zero-+ : ∀ (n : ℕ) → 0 + n ≡ n
zero-+ n = refl


-- In the standard library: +-identityʳ
+-zero : ∀ (n : ℕ) → n + 0 ≡ n
+-zero zero    = refl
+-zero (suc k) = cong suc (+-zero k)
    -- let ih = +-zero k in
    --   cong suc ih

suc-+ : ∀ (m n : ℕ) → (suc m) + n ≡ suc (m + n)
suc-+ m n = refl

+-suc : ∀ (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc k) n = cong suc (+-suc k n)
    -- let ih = +-suc m n in
    --   cong suc ih

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero    n = begin
  0 + n  ≡⟨ zero-+ n ⟩
  n      ≡⟨ sym (+-zero n) ⟩
  n + 0  ∎
  -- trans (zero-+ n) (sym (+-zero n))
+-comm (suc m) n = begin
  (suc m) + n  ≡⟨ suc-+ m n ⟩
  suc (m + n)  ≡⟨ cong suc (+-comm m n) ⟩
  suc (n + m)  ≡⟨ sym (+-suc n m) ⟩
  n + (suc m)  ∎
  -- trans (suc-+ m n)
  --       (trans (cong suc (+-comm m n))
  --              (sym (+-suc n m)))


*-zero : ∀ (n : ℕ) → n * 0 ≡ 0
*-zero zero    = refl
*-zero (suc n) = *-zero n


*-one : ∀ (n : ℕ) → n * 1 ≡ n
*-one zero    = refl
*-one (suc n) = begin
  (suc n) * 1  ≡⟨ refl ⟩
  1 + (n * 1)  ≡⟨ refl ⟩
  suc (n * 1)  ≡⟨ cong suc (*-one n) ⟩
  suc n        ∎


one-* : ∀ (n : ℕ) → 1 * n ≡ n
one-* n = +-zero n
