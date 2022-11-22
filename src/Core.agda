{-# OPTIONS --guardedness  #-}
{-# OPTIONS --type-in-type #-}

module Core where

open import Cases
open import Data.Maybe
open import Data.Product hiding (_<*>_; map)
open import Function using (_↔_; const)
open import Relation.Binary.PropositionalEquality
open import Shape

open Function.Inverse renaming (f to fwd; f⁻¹ to bwd)


postulate
  oracle
    : {Idx : Set}
    → {rep : Idx → Set → Set}
    → {i o : Generic}
    → (_∙_ : Shape → Shape → Shape)
    → (spec : (idx : Idx) → {A : Set} → i (rep idx) A      → o (rep idx) A)
    → Maybe ( {l r : Shape}
            → (f : Poly i o l)
            → (g : Poly i o r)
            → Poly i o (l ∙ r)
            )


synthesize
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
    → (i-nat : Natural i) → (o-nat : Natural o)
      -- We have a specification for every index
    → (spec : (idx : Idx) → {A : Set} → i (rep idx) A → o (rep idx) A)
      -- we can thus build a set of cases such that
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
        → map (λ { f → f {A} x }) (implement cases r)
        ≡ just (o-nat (same .bwd) (spec idx {A} (i-nat (same .fwd) x)))
      )
proj₁ (synthesize conv build i-nat o-nat spec) V
    with build V1
... | just (idx , bij)
    = just (V1C λ { x → o-nat (bij .bwd) (spec idx (i-nat (bij .fwd) x)) } )
... | nothing = nothing
proj₁ (synthesize conv build i-nat o-nat spec) K = {! !}
proj₁ (synthesize conv build i-nat o-nat spec) U
    with build U1
... | just (idx , bij)
    = just (U1C λ { x → o-nat (bij .bwd) (spec idx (i-nat (bij .fwd) x)) })
... | nothing = nothing
proj₁ (synthesize {i = i} {o} conv build i-nat o-nat spec) Plus
    with oracle {i = i} {o} _:+:_ spec
... | just result
    = just (+C λ { {l} {r} f g {a} x → result {l} {r} f g {a} x })
... | nothing = nothing
proj₁ (synthesize {i = i} {o} conv build i-nat o-nat spec) Times
    with oracle {i = i} {o} _:*:_ spec
... | just result
    = just (*C λ { {l} {r} f g {a} x → result {l} {r} f g {a} x })
... | nothing = nothing
proj₁ (synthesize conv build i-nat o-nat spec) P
    with build Par1
... | just (idx , bij)
    = just (P1C λ { x → o-nat (bij .bwd) (spec idx (i-nat (bij .fwd) x)) })
... | nothing = nothing
proj₂ (synthesize conv build i-nat o-nat spec) A idx r same x = {! todo: prove me! !}

