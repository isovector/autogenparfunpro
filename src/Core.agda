module Core where

open import Cases
open import Data.Maybe
open import Data.Product hiding (_<*>_; map)
open import Function using (_↔_; const; _∘_)
open import Relation.Binary.PropositionalEquality
open import Shape
open import Data.Nat
open import Factor

open Function.Inverse renaming (f to fwd; f⁻¹ to bwd)

open import Data.Vec


rep : ℕ → Set → Set
rep n A = Vec A n


postulate
  oracle
    : {i o : Generic}
    → (_∙_ : Shape → Shape → Shape)
    -- TODO(sandy): spec has the wrong type to be useful! It's in terms of
    -- indices, but we need it in terms of shapes.
    → (spec : (idx : ℕ) → {A : Set} → i (rep idx) A → o (rep idx) A)
    → ( {l r : Shape}
      → (f : Poly i o l)
      → (g : Poly i o r)
      → Poly i o (l ∙ r)
      )

optimize
    : -- Then, we have an input and output type family
      {i o : Generic}

      -- We have natural transformations over i and o
    → (i-nat : Natural i)
    → (o-nat : Natural o)

      -- We have a specification for every index
    → (spec : (idx : ℕ) → {A : Set} → i (rep idx) A → o (rep idx) A)

      -- Given all this, we can thus build a set of cases such that...
    → Σ (Cases i o) λ cases →
      (∀ (A : Set)

        -- for any index that is isomorphic to a given shape
        → (idx : ℕ)
        → (r : Shape)
        → (factor : Factorization idx r)

        -- and some given input
        → (x : Instantiated i r A)

        -- we show that our cases compose together to produce the same answer
        -- as the specification
        → implement cases r x ≡ o-nat (fromVec factor) (spec idx (i-nat (toVec factor) x))
      )

proj₁ (optimize i-nat o-nat spec) U             = U1C λ { x             → o-nat (fromVec u) (spec 0 (i-nat (toVec u) x))}
proj₁ (optimize i-nat o-nat spec) P             = P1C λ { x             → o-nat (fromVec a) (spec 1 (i-nat (toVec a) x))}
proj₁ (optimize {i} {o} i-nat o-nat spec) Times = *C  λ { {l} {r} f g x → oracle {i} {o} _:*:_ spec {l} {r} f g x }
proj₁ (optimize {i} {o} i-nat o-nat spec) Comp  = ∘C  λ { {l} {r} f g x → oracle {i} {o} _:∘:_ spec {l} {r} f g x }
proj₂ (optimize i-nat o-nat spec)               = {! !}

