module Lambdas.Examples where

open import Lambdas.Language

three : Term
three = `suc (`suc (`suc `zero))

five : Term
five = `suc (`suc three)

nat-id : Term
nat-id = `λ "x" ⦂ Nat ⇒ ` "x"

nat-id-app : Term
nat-id-app = nat-id · three

func : Term
func = (`λ "f" ⦂ (Bool ⇒ Bool) ⇒
         (`λ "x" ⦂ Bool ⇒
           (` "f" · (`if (` "x") `false (` "x")))))

free-vars : Term
free-vars = (` "f") · (` "x")

_ : (`λ "x" ⦂ Nat ⇒ (`if (`zero? (` "x")) three five)) · three —→* five
_ = begin
    (`λ "x" ⦂ Nat ⇒ (`if (`zero? (` "x")) three five)) · three
  —→⟨ subst (V-nat (NV-suc (NV-suc (NV-suc NV-zero)))) ⟩
    `if (`zero? three) three five
  —→⟨ reduce-if (zero?-suc (NV-suc (NV-suc NV-zero))) ⟩
    `if `false three five
  —→⟨ if-false ⟩
    five
  ∎
