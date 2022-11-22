{-# OPTIONS --guardedness  #-}

module Core where

open import Cases
open import Data.Maybe
open import Data.Product hiding (_<*>_; map)
open import Function using (_↔_; const)
open import Relation.Binary.PropositionalEquality
open import Shape

open Function.Inverse renaming (f to fwd; f⁻¹ to bwd)


postulate
  synthesizer-oracle
    : {Idx : Set}
    → {rep : Idx → Set → Set}
    → {i o : Generic}
    → (_∙_ : Shape → Shape → Shape)
    -- TODO(sandy): spec has the wrong type to be useful! It's in terms of
    -- indices, but we need it in terms of shapes.
    → (spec : (idx : Idx) → {A : Set} → i (rep idx) A → o (rep idx) A)
    → Maybe ( {l r : Shape}
            → (f : Poly i o l)
            → (g : Poly i o r)
            → Poly i o (l ∙ r)
            )

optimize
      -- All of our representations are indexed by some arbitrary type
      -- we make the assumption that this is a total mapping
    : {Idx : Set}
    → {rep : Idx → Set → Set}

      -- Then, we have an input and output type family
    → {i o : Generic}

      -- For any given shape, we can decide whether there is an index which
      -- gives rise to this shape; as well as show the equivalence between the
      -- functor shape and the representation itself
    → (convert : (idx : Idx) → Σ Shape λ s → {A : Set} → interpret s A ↔ rep idx A)
    → (build : (s : Shape) → Maybe (Σ Idx λ idx → {A : Set} → interpret s A ↔ rep idx A))

      -- We have natural transformations over i and o
    → (i-nat : Natural i)
    → (o-nat : Natural o)

      -- We have a specification for every index
    → (spec : (idx : Idx) → {A : Set} → i (rep idx) A → o (rep idx) A)

      -- Given all this, we can thus build a set of cases such that...
    → Σ (Cases i o) λ cases →
      (∀ (A : Set)

        -- for any index that is isomorphic to a given shape
        → (idx : Idx)
        → (r : Shape)
        → (same : {X : Set} → interpret r X ↔ rep idx X)

        -- and some given input
        → (x : Instantiated i r A)

        -- we show that our cases compose together to produce the same answer
        -- as the specification
        → map (λ { f → f {A} x }) (implement cases r) ≡ just (o-nat (same .bwd) (spec idx {A} (i-nat (same .fwd) x)))
      )


-- In order to give a case for V, attempt to build at V1
proj₁ (optimize conv build i-nat o-nat spec) V
    with build V1
... | nothing = nothing
    -- If we are successful, we get an index and bijection that is equivalent to void
... | just (idx , bij)
    -- In which case we can just chase the diagram to implement this case
    = just (V1C λ { x → o-nat (bij .bwd) (spec idx (i-nat (bij .fwd) x)) } )

-- Likewise for U
proj₁ (optimize conv build i-nat o-nat spec) U
    with build U1
... | nothing = nothing
... | just (idx , bij)
    = just (U1C λ { x → o-nat (bij .bwd) (spec idx (i-nat (bij .fwd) x)) })

-- Likewise for Par1
proj₁ (optimize conv build i-nat o-nat spec) P
    with build Par1
... | nothing = nothing
... | just (idx , bij)
    = just (P1C λ { x → o-nat (bij .bwd) (spec idx (i-nat (bij .fwd) x)) })

-- Plus and times are hard; there's no diagram chasing to do, because we'd need
-- to commit to a success before we have anything we can even look at. Instead,
-- invoke the synthesizer-oracle to solve it for us.
proj₁ (optimize {i = i} {o} conv build i-nat o-nat spec) Plus
    with synthesizer-oracle {i = i} {o} _:+:_ spec
... | just result
    = just (+C λ { {l} {r} f g {a} x → result {l} {r} f g {a} x })
... | nothing = nothing
proj₁ (optimize {i = i} {o} conv build i-nat o-nat spec) Times
    with synthesizer-oracle {i = i} {o} _:*:_ spec
... | just result
    = just (*C λ { {l} {r} f g {a} x → result {l} {r} f g {a} x })
... | nothing = nothing

-- It's unclear what to do for constant types right now, since there are
-- potentially infinitely many of them. But I don't expect this to be an
-- interesting problem.
proj₁ (optimize conv build i-nat o-nat spec) K = {! !}

-- All thats left is to prove it all holds.
proj₂ (optimize conv build i-nat o-nat spec) A idx r same x = {! todo: prove me! !}

