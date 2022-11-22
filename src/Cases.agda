module Cases where

open import Shape
open import Data.Maybe

-- Functor recursive cases for our algorithm
data Case (i : Generic) (o : Generic) : Head → Set₁ where
  V1C : Poly i o V1 → Case i o V
  U1C : Poly i o U1 → Case i o U
  KC : ({x : Set} → Poly i o (K1 x)) → Case i o K
  +C : ( {l r : Shape}
       → (f : Poly i o l)
       → (g : Poly i o r)
       → Poly i o (l :+: r)
       )
     → Case i o Plus
  *C : ( {l r : Shape}
       → (f : Poly i o l)
       → (g : Poly i o r)
       → Poly i o (l :*: r)
       )
     → Case i o Times
  P1C : Poly i o Par1 → Case i o P
  -- R1C : Poly i o Rec1 → Case i o R

-- A function from heads to cases of it
Cases : ∀ i o → Set₁
Cases i o = (h : Head) → Maybe (Case i o h)


-- Transform Cases into a transformation for the given shape
implement
    : {i o : (Set → Set) → Set → Set}
    → (cases : Cases i o)
    → (r : Shape)
    → Maybe (Poly i o r)
implement cases r with cases (caseOf r)
implement cases r | nothing = nothing
implement cases V1 | just (V1C f) = just f
implement cases U1 | just (U1C f) = just f
implement cases (K1 f₁) | just (KC f) = just f
implement cases (l :+: r) | just (+C f) with implement cases l  | implement cases r
implement cases (l :+: r) | just (+C f) | just x | just y = just (f {l} {r} x y)
implement cases (l :+: r) | just (+C f) | _ | _ = nothing
implement cases (l :*: r) | just (*C f) with implement cases l  | implement cases r
implement cases (l :*: r) | just (*C f) | just x | just y = just (f {l} {r} x y)
implement cases (l :*: r) | just (*C f) | _ | _ = nothing
implement cases Par1 | just (P1C f) = just f

