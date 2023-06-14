-- Simple model for parallel computation.
-- The postulates are exercises.

module Parallel where

open import Data.Product
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality

private variable m n o : ℕ

-- Bit vector
𝔹* : ℕ → Set
𝔹* n = Vec 𝔹 n

-- Single operation consuming n bits and yielding one.
-- We could generalize to yield m bits.
data Op : ℕ → Set where
  `ix : ∀ (i : Fin n) → Op n
  `not : Op 1
  `and `or : Op 2

postulate
  ⟦_⟧ᵒ : Op n → (𝔹* n → 𝔹)

-- Parallel composition of operations sharing an input vector.
infix 0 _↠_
_↠_ :  ℕ → ℕ → Set
m ↠ n = Vec (Op m) n

postulate
  ⟦_⟧₁ : (m ↠ n) → (𝔹* m → 𝔹* n)

-- Sequential composition of parallel compositions
infix  0 _⇨_
infixr 5 _∷_
data _⇨_ :  ℕ → ℕ → Set where
  [] : n ⇨ n
  _∷_ : (m ↠ n) → (n ⇨ o) → (m ⇨ o)

postulate
  ⟦_⟧ : (m ⇨ n) → (𝔹* m → 𝔹* n)

private variable f g : m ⇨ n

infixr 9 _∘′_
postulate

  id′ : n ⇨ n
  _∘′_ : (n ⇨ o) → (m ⇨ n) → (m ⇨ o)

  ⟦id⟧ : ⟦ id′ {n} ⟧ ≗ id
  ⟦∘⟧  : ⟦ g ∘′ f ⟧  ≗ ⟦ g ⟧ ∘ ⟦ f ⟧


postulate
  depth : (m ⇨ n) → ℕ -- number of parallel phases
  work  : (m ⇨ n) → ℕ -- number of non-`ix operations

has-depth : (𝔹* m → 𝔹* n) → ℕ → Set
has-depth f d = ∃ λ f′ → ⟦ f′ ⟧ ≗ f × depth f′ ≡ d

has-work : (𝔹* m → 𝔹* n) → ℕ → Set
has-work f d = ∃ λ f′ → ⟦ f′ ⟧ ≗ f × work f′ ≡ d

-- Exercise: prove depth and work for a monoidal reduction (e.g., ∧).


-- TODO: How to define fork/?
