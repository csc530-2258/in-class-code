module EvenOdd where

-- This is the proof that all natural numbers are even or odd but now
-- in Agda!  It may look a little simpler than it did in Pie.

-- NOTE: We haven't learned several of these things in class yet, but
-- we will!

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; module ≡-Reasoning)

open ≡-Reasoning

-- Using this definition of double, the proof that 1+even->odd and
-- 1+odd->even will be easier.  I prove at the end that
-- double n ≡ n + n.
double : ℕ → ℕ
double zero    = zero
double (suc n) = 2 + double n

IsEven : ℕ → Set
IsEven n = ∃[ k ] n ≡ double k

IsOdd : ℕ → Set
IsOdd n = ∃[ k ] n ≡ 1 + double k

zero-even : IsEven 0
zero-even = 0 , refl

1+even->odd : ∀ n → IsEven n → IsOdd (suc n)
1+even->odd n (k , n≡2k) = k , cong suc n≡2k

1+odd->even : ∀ n → IsOdd n → IsEven (suc n)
1+odd->even n (k , n≡1+2k) = 1 + k , cong suc n≡1+2k

even-or-odd : ∀ n → IsEven n ⊎ IsOdd n
even-or-odd zero    = inj₁ zero-even
even-or-odd (suc n) with even-or-odd n
... | inj₁ n-even = inj₂ (1+even->odd n n-even)
... | inj₂ n-odd  = inj₁ (1+odd->even n n-odd)


-- If my definition of double had been n + n, I could have still done
-- the above proofs (the definition is numerically equivalent), but
-- they would have required more algebra to work.  A similar proof
-- could be done for a version of double that returned 2 * n.
double≡n+n : ∀ n → double n ≡ n + n
double≡n+n zero    = refl
double≡n+n (suc n) = begin
  double (suc n)        ≡⟨ refl ⟩
  suc (suc (double n))  ≡⟨ cong (λ x → suc (suc x)) (double≡n+n n) ⟩
  suc (suc (n + n))     ≡⟨ cong suc (sym (+-suc n n)) ⟩
  suc (n + suc n)       ≡⟨ refl ⟩
  suc n + suc n         ∎
