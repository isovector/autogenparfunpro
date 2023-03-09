module Cases where

open import Shape
open import Data.Maybe

-- Functor recursive cases for our algorithm
data Case (i : Generic) (o : Generic) : Head → Set₁ where
  V1C : Poly i o V1 → Case i o V
  U1C : Poly i o U1 → Case i o U
  ∘C : ( {l r : Shape}
       → (f : Poly i o l)
       → (g : Poly i o r)
       → Poly i o (l :∘: r)
       )
     → Case i o Comp
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
Cases i o = (h : Head) → Case i o h


-- Transform Cases into a transformation for the given shape
implement
    : {i o : (Set → Set) → Set → Set}
    → (cases : Cases i o)
    → (r : Shape)
    → Poly i o r
implement cases V1 with cases V
... | V1C x = x
implement cases U1 with cases U
... | U1C x = x
implement cases (l :*: r) with cases Times | implement cases l | implement cases r
... | *C x | z | y = x {l} {r} z y
implement cases (l :∘: r) with cases Comp | implement cases l | implement cases r
... | ∘C x | z | y = x {l} {r} z y
implement cases Par1 with cases P
... | P1C x = x

