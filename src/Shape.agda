module Shape where

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (_<*>_; map)
open import Data.Sum hiding (map)

infixr 5 _:+:_
infixr 6 _:*:_

-- Reified shape of a data type
data Shape : Set₁ where
  V1 : Shape
  U1 : Shape
  K1 : Set → Shape
  _:+:_ : Shape → Shape → Shape
  _:*:_ : Shape → Shape → Shape
  Par1 : Shape
  -- Rec1 : Shape

mutual
  -- record μ (r : Shape) (v : Set) : Set where
  --   inductive
  --   pattern
  --   constructor fix
  --   field
  --     getfix : interpret r v

  go : Shape → Set → Set
  go V1 v = ⊥
  go U1 v = ⊤
  go (K1 x) v = x
  go (x :+: y) v = go x v ⊎ go y v
  go (x :*: y) v = go x v × go y v
  go Par1 v = v
  -- go Rec1 v = ? -- μ r v

  -- Evaluate a shape and a parameter into a type in Set
  interpret : Shape → Set → Set
  interpret r v = go r v

-- The instance heads we need to give algorithm instances for
data Head : Set where
  V K U Plus Times P : Head


-- Get the head of a shape
caseOf : Shape → Head
caseOf V1 = V
caseOf U1 = U
caseOf (K1 x) = K
caseOf (x :+: x₁) = Plus
caseOf (x :*: x₁) = Times
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

