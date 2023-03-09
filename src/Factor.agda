module Factor where

open import Data.Nat
open import Shape
open import Data.Product
open import Data.Unit
open import Data.Vec
open import Function

private variable
  A : Set
  n n₁ n₂ : ℕ
  s s₁ s₂ : Shape

-- Witness a bijection between the index and ways of building a vector with that size.
data Factorization : ℕ → Shape → Set where
  u : Factorization 0 U1
  a : Factorization 1 Par1
  p : Factorization n₁ s₁ → Factorization n₂ s₂ → Factorization (n₁ + n₂) (s₁ :*: s₂)
  c : Factorization n₁ s₁ → Factorization n₂ s₂ → Factorization (n₁ * n₂) (s₁ :∘: s₂)


toVec : Factorization n s → interpret s A → Vec A n
toVec u x₁ = []
toVec a x₁ = x₁ ∷ []
toVec (p x x₂) (fst , snd) = toVec x fst ++ toVec x₂ snd
toVec (c {n₁} {s₁ = s₁} {n₂} {s₂ = s₂} x x₂) x₁
 = concat (toVec x (fmap s₁ (toVec x₂) x₁))

fromVec : Factorization n s → Vec A n → interpret s A
fromVec u x₁ = tt
fromVec a (x ∷ []) = x
fromVec (p {n₁} x x₂) x₁ with splitAt n₁ x₁
... | v1 , v2 , _ = fromVec x v1 , fromVec x₂ v2
fromVec (c {n₁} {s₁} {n₂} {s₂} x x₂) x₁ with group n₁ n₂ x₁
... | fst , _ = fromVec x (Data.Vec.map (fromVec x₂) fst)


