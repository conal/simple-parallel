-- Simple model for parallel evaluation.

module Parallel where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.Nat
open import Data.Fin
open import Data.Vec

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

⟦_⟧ˢ : Op n → (𝔹* n → 𝔹)
⟦ `ix i ⟧ˢ xs           = lookup xs i
⟦ `not  ⟧ˢ (x ∷ [])     = not x
⟦ `and  ⟧ˢ (x ∷ y ∷ []) = x ∧ y
⟦ `or   ⟧ˢ (x ∷ y ∷ []) = x ∨ y

-- One parallel step: operations in parallel, sharing an input vector.
infix 0 _↠_
_↠_ :  ℕ → ℕ → Set
m ↠ n = Vec (Op m) n

⟦_⟧₁ : (m ↠ n) → (𝔹* m → 𝔹* n)
⟦ ops ⟧₁ xs = map (λ op → ⟦ op ⟧ˢ xs) ops

id′ : n ↠ n
id′ = tabulate `ix

not′ : 1 ↠ 1
not′ = `not ∷ []

and′ or′ : 2 ↠ 1
and′ = `and ∷ []
or′  = `or  ∷ []

infix 0 _⇨_
infixr 5 _∷_
data _⇨_ :  ℕ → ℕ → Set where
  [] : n ⇨ n
  _∷_ : (m ↠ n) → (n ⇨ o) → (m ⇨ o)

id″ : n ⇨ n
id″ = tabulate `ix ∷ []

op : Op n → (n ⇨ 1)
op o = (o ∷ []) ∷ []

not″ : 1 ⇨ 1
not″ = op `not

and″ or″ : 2 ⇨ 1
and″ = op `and
or″  = op `or

open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality

-- ⟦id′⟧ : ⟦ id′ ⟧ ≗ id
