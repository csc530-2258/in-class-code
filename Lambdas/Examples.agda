module Lambdas.Examples where

open import Data.Nat using (ℕ)
open import Lambdas.Language
open import Lambdas.Properties
open import Relation.Binary.PropositionalEquality
  using (_≢_)

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

_ : "z" ⦂ Nat ∈ (∅ , "x" ⦂ Nat ⇒ Nat , "y" ⦂ Bool , "z" ⦂ Nat)
_ = here

_ : "x" ⦂ Nat ⇒ Nat ∈ (∅ , "x" ⦂ Nat ⇒ Nat , "y" ⦂ Bool , "z" ⦂ Nat)
_ = there (λ ()) (there (λ ()) here)

program : Term
program =
  (`λ "x" ⦂ Nat ⇒ (`if (`zero? (` "x")) three five)) · three

program-nat : ∅ ⊢ program ⦂ Nat
program-nat = ⊢app
  (⊢lam
   (⊢if (⊢zero? (⊢var here)) (⊢suc (⊢suc (⊢suc ⊢zero)))
    (⊢suc (⊢suc (⊢suc (⊢suc (⊢suc ⊢zero)))))))
  (⊢suc (⊢suc (⊢suc ⊢zero)))
