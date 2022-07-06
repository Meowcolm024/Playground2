open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe public

record Functor {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixl 4 _<$>_ 
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap

record Applicative {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixl 4 _<*>_ 
  field
    pure : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    overlap {{super}} : Functor F

record Monad {a b} (M : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixl 1 _>>=_
  field
    _>>=_ : ∀ {A B} → M A → (A → M B) → M B
    overlap {{super}} : Applicative M

record Alternative {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixl 3 _<|>_
  field
    _<|>_ : ∀ {A} → F A → F A → F A
    overlap {{super}} : Applicative F

open Functor {{...}} public
open Applicative {{...}} public
open Monad {{...}} public
open Alternative {{...}} public

maybe : ∀ {a b} {A : Set a} {B : Set b} → B → (A → B) → Maybe A → B
maybe z f nothing  = z
maybe z f (just x) = f x

map : ∀ {a} {A : Set a} {B : Set a} → (A → B) → Maybe A → Maybe B
map f m = maybe nothing (λ x → just (f x)) m

instance 
  FunctorMaybe : ∀ {a} → Functor (Maybe {a})
  FunctorMaybe = record {fmap = map}

instance
  ApplicativeMaybe : ∀ {a} → Applicative (Maybe {a})
  ApplicativeMaybe = record {
    pure = just ;
    _<*>_ = λ mf mx → maybe nothing (λ f → fmap f mx) mf
    }

instance
  MonadMaybe : ∀ {a} → Monad (Maybe {a})
  MonadMaybe = record {_>>=_ = λ x f → maybe nothing f x}

instance 
  AlternativeMaybe : ∀ {a} → Alternative (Maybe {a})
  AlternativeMaybe = record {_<|>_ = λ l r → maybe r just l}

add1 : Nat → Maybe Nat
add1 0 = just 1
add1 _ = nothing

prog : Maybe Nat
prog = do
  x <- nothing <|> just 0
  res <- add1 x
  pure (res * 2)
