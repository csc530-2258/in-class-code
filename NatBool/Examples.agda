module NatBool.Examples where

open import NatBool.Language

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
