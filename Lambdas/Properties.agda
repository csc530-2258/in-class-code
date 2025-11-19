module Lambdas.Properties where

open import Lambdas.Language

open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)

Normal : Term → Set
Normal t = ∀ {t′} → ¬ (t —→ t′)

Stuck : Term → Set
Stuck t = Normal t × ¬ (Value t)
