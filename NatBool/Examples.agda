module NatBool.Examples where

open import NatBool.Language
open import NatBool.Properties

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)


three : Term
three = `suc (`suc (`suc `zero))

five : Term
five = `suc (`suc three)

program1 : Term
program1 = `if `true three five

program2 : Term
program2 = `if (`zero? three) three five

program3 : Term
program3 = `suc `true

three-is-val : Value three
three-is-val = V-nat (NV-suc (NV-suc (NV-suc NV-zero)))

two-is-natval : NatValue (`suc (`suc `zero))
two-is-natval = NV-suc (NV-suc NV-zero)

prog3-not-val : ¬ (Value program3)
prog3-not-val (V-bool ())
prog3-not-val (V-nat (NV-suc ()))

p1-step : program1 —→ three
p1-step = if-true

p2-step : program2 —→ `if `false three five
p2-step = reduce-if (zero?-suc two-is-natval)

p3-no-step : ∀ {t} → ¬ (program3 —→ t)
p3-no-step (reduce-suc ())

p3-stuck : Stuck program3
p3-stuck = p3-no-step , prog3-not-val

p2-steps : program2 —→* five
p2-steps = multi-steps (reduce-if (zero?-suc two-is-natval))
                       (multi-steps if-false no-steps)

three-is-nat : ⊢ three ⦂ Nat
three-is-nat = ⊢suc (⊢suc (⊢suc ⊢zero))

p2-is-nat : ⊢ program2 ⦂ Nat
p2-is-nat = ⊢if (⊢zero? three-is-nat)
                three-is-nat
                (⊢suc (⊢suc three-is-nat))

p3-has-no-type : ∀ {T : Type} → ¬ (⊢ program3 ⦂ T)
p3-has-no-type (⊢suc ())
