module Example where

open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Vec hiding (map)
open import Relation.Binary.PropositionalEquality hiding (cong₂; [_])
open import Shape

open import Function using (_↔_; const)
open Function.Inverse renaming (f to fwd; f⁻¹ to bwd)


buildVec : (s : Shape) → Maybe (Σ ℕ λ n → {A : Set} → interpret s A ↔ Vec A n)
buildVec V1 = nothing
buildVec U1 = just
  ( 0
  , record
      { f = const []
      ; f⁻¹ = const tt
      ; cong₁ = const refl
      ; cong₂ = const refl
      ; inverse = (λ { [] → refl }) , λ { tt → refl }
      }
  )
buildVec (K1 x) = nothing
buildVec (s :+: s₁) = nothing
buildVec (l :*: r) with buildVec l | buildVec r
... | just (pi , pbij) | just (qi , qbij) = just
  ( pi + qi
  , record
      { f = λ { (fst , snd) → pbij .fwd fst ++ qbij .fwd snd }
      ; f⁻¹ = λ { x → let (l , (r , proof)) = splitAt pi {qi} x
                       in pbij .bwd l
                        , qbij .bwd r
                }
      ; cong₁ = exercise-for-the-reader
      ; cong₂ = exercise-for-the-reader
      ; inverse = exercise-for-the-reader
      }
  )
  where
    postulate exercise-for-the-reader : {A : Set} → A
... | _ | _ = nothing
buildVec Par1 = just
  (1
  , record
      { f = [_]
      ; f⁻¹ = head
      ; cong₁ = λ { x → cong (_∷ []) x }
      ; cong₂ = λ { x → cong head x }
      ; inverse = (λ { (x ∷ []) → refl })
                 , λ { x → refl }
      }
  )
