module Shape where

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (_<*>_; map)
open import Data.Sum hiding (map)

infixr 5 _:*:_
infixr 6 _:∘:_

-- Reified shape of a data type
data Shape : Set₁ where
  U1 : Shape
  _:*:_ : Shape → Shape → Shape
  _:∘:_ : Shape → Shape → Shape
  Par1 : Shape
  -- Rec1 : Shape

interpret : Shape → Set → Set
interpret U1 v = ⊤
interpret (x :*: y) v = interpret x v × interpret y v
interpret (x :∘: y) v = interpret x (interpret y v)
interpret Par1 v = v

fmap : (s : Shape) {A B : Set} → (A → B) → interpret s A → interpret s B
fmap U1 f x = tt
fmap (s :*: s₁) f (x₁ , x₂) = fmap s f x₁ , fmap s₁ f x₂
fmap (s :∘: s₁) f x = fmap s (fmap s₁ f) x
fmap Par1 f x = f x

-- The instance heads we need to give algorithm instances for
data Head : Set where
  U Times Comp P : Head


-- Get the head of a shape
caseOf : Shape → Head
caseOf U1 = U
caseOf (x :*: x₁) = Times
caseOf (x :∘: x₁) = Comp
caseOf Par1 = P
-- caseOf Rec1 = R


-- The type of generic things
Generic : Set₁
Generic = (Set → Set) → Set → Set

-- Instantiate a generic by interpreting the shape as its first argument
Instantiated : Generic → Shape → Set → Set
Instantiated i s a = i (interpret s) a

-- A function from one generic to another
Transform : Generic → Generic → Shape → Set → Set
Transform i o s a = Instantiated i s a → Instantiated o s a

-- A polymorphic Transform
Poly : Generic → Generic → Shape → Set₁
Poly i o s = {a : Set} → Transform i o s a

-- A natural transformation over a generic type
Natural : Generic → Set₁
Natural i = {F G : Set → Set} {A : Set} → ({X : Set} → F X → G X) → i F A → i G A

