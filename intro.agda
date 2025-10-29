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


-- In the standard library: +-identityˡ
zero-+ : ∀ (n : ℕ) → 0 + n ≡ n
zero-+ n = refl


-- In the standard library: +-identityʳ
+-zero : ∀ (n : ℕ) → n + 0 ≡ n
+-zero zero    = refl
+-zero (suc k) = cong suc (+-zero k)
    -- let ih = +-zero k in
    -- cong suc ih


-- coming soon
-- +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
-- +-comm = {!   !}
