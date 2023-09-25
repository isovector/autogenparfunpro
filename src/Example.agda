module Example where

open import Core
open import Cases
open import Data.Maybe hiding (map)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Unit
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (cong₂; [_])
open import Shape
open import Algebra.Definitions

open import Function using (_↔_; const; flip)
open Function.Inverse renaming (f to fwd; f⁻¹ to bwd)


private postulate
  exercise-for-the-reader : {A : Set} → A


Idx : Set
Idx = ℕ


convert : (n : ℕ) → (Σ Shape λ s → {A : Set} → interpret s A ↔ Vec A n)
convert zero = U1
  , record
      { f = const []
      ; f⁻¹ = const tt
      ; cong₁ = const refl
      ; cong₂ = const refl
      ; inverse = (λ { [] → refl }) , λ { tt → refl }
      }
convert (suc n) with convert n
... | (s , bij)
    = Par1 :*: s
    , record
        { f = λ { (fst , snd) → fst ∷ bij .fwd snd }
        ; f⁻¹ = λ { (x ∷ xs) → x , bij .bwd xs }
        ; cong₁ = λ { refl → refl }
        ; cong₂ = λ { refl → refl }
        ; inverse = (λ { (x ∷ xs)    → cong (x ∷_)   (proj₁ (bij .inverse) xs)  })
                  ,  λ { (fst , snd) → cong (fst ,_) (proj₂ (bij .inverse) snd) }
        }


build : (s : Shape) → Maybe (Σ ℕ λ n → {A : Set} → interpret s A ↔ Vec A n)
build V1 = nothing
build U1 = just ( 0 , proj₂ (convert 0) )
build (s :+: s₁) = nothing
build (l :*: r) with build l | build r
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
... | _ | _ = nothing
build Par1 = just
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


record Monoid (A : Set) : Set where
  field
    mempty : A
    _<>_ : A → A → A
    <>-unitˡ : LeftIdentity _≡_ mempty _<>_
    <>-unitʳ : RightIdentity _≡_ mempty _<>_
    <>-assoc : Associative _≡_ _<>_

open Monoid

module _ where
  open import Data.Nat.Properties

  ℕ-Monoid : Monoid ℕ
  mempty ℕ-Monoid = 0
  _<>_ ℕ-Monoid = _+_
  <>-unitˡ ℕ-Monoid = +-identityˡ
  <>-unitʳ ℕ-Monoid = +-identityʳ
  <>-assoc ℕ-Monoid = +-assoc


i : Generic
i f a = Monoid a × f a

i-natural : Natural i
i-natural f (fst , snd) = fst , f snd


o : Generic
o f a = f a × a

o-natural : Natural o
o-natural f (fst , snd) = f fst , snd


rep : ℕ → Set → Set
rep = flip Vec

spec : (n : ℕ) → {A : Set} → i (rep n) A → o (rep n) A
spec .zero (mon , []) = [] , mon .mempty
spec .1 (mon , x ∷ []) = mon .mempty ∷ [] , x
spec (suc (suc n)) (mon , x₁ ∷ x₂ ∷ xs) with spec (suc n) (mon , x₂ ∷ xs)
... | fa , res = mon .mempty ∷ map (mon ._<>_ x₁) fa , mon ._<>_ x₁ res


module UnitTests where
  _ : spec _ (ℕ-Monoid , 1 ∷ 1 ∷ 1 ∷ 1 ∷ [])
    ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [] , 4)
  _ = refl


solution : Cases i o
solution = proj₁ (optimize convert build i-natural o-natural spec)

