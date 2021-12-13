{-# OPTIONS --guardedness #-}

module aoc-01-p2 where

open import Data.Bool hiding (_<_)
open import Data.Nat
open import Data.List renaming (map to mapₗ)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function

Sample : Set
Sample = ℕ

observe : ∀ {A : Set} → (List A → Sample → List A) → List Sample → List A
observe memorizer = reverse ∘ foldl memorizer []

data Memory3 : Set where
  mem3-one : Sample → Memory3
  mem3-two : Sample → Sample → Memory3
  mem3-three : Sample → Sample → Sample → Memory3

memorizer3 : List Memory3 → Sample → List Memory3
memorizer3 [] s = [ mem3-one s ]
memorizer3 (mem3-one x ∷ l) s = mem3-two s x ∷ mem3-one x ∷ l
memorizer3 (mem3-two x x₁ ∷ l) s = mem3-three s x x₁ ∷ mem3-two x x₁ ∷ l
memorizer3 (mem3-three x x₁ x₂ ∷ l) s = mem3-three s x x₁ ∷ mem3-three x x₁ x₂ ∷ l

ex1 : List Sample
ex1 = 200 ∷ 201 ∷ 201 ∷ [ 200 ]

obs1 = mem3-one 200
     ∷ mem3-two 201 200
     ∷ mem3-three 201 201 200
     ∷ [ mem3-three 200 201 201 ]

test1 : observe memorizer3 ex1 ≡ obs1
test1 = refl

summarize : List Memory3 → List Sample
summarize [] = []
summarize (mem3-one x ∷ l) = summarize l
summarize (mem3-two x x₁ ∷ l) = summarize l
summarize (mem3-three x x₁ x₂ ∷ l) = (x + x₁ + x₂) ∷ (summarize l)

sum1 = 602
     ∷ [ 602 ]
test2 : (summarize ∘ observe memorizer3) ex1 ≡ sum1
test2 = refl

data Memory2 : Set where
  mem2-one : Sample → Memory2
  mem2-two : Sample → Sample → Memory2

memorizer2 : List Memory2 → Sample → List Memory2
memorizer2 [] s = [ mem2-one s ]
memorizer2 (mem2-one x ∷ l) s = mem2-two s x ∷ mem2-one x ∷ l
memorizer2 (mem2-two x x₁ ∷ l) s = mem2-two s x ∷ mem2-two x x₁ ∷ l

data Variation : Set where
  na : Variation
  increased : Variation
  decreased : Variation
  no-change : Variation

analyzer : Memory2 → Variation
analyzer (mem2-one x) = na
analyzer (mem2-two x x₁) =  if x₁ <ᵇ x
                         then increased
                         else (if x <ᵇ x₁
                               then decreased
                               else no-change)

analyze : List Memory2 → List Variation
analyze = mapₗ analyzer

an1 : List Variation
an1 = na ∷ [ no-change ]
test3 : ( analyze ∘ (observe memorizer2) ∘ summarize ∘ observe memorizer3) ex1 ≡ an1
test3 = refl

count-aux : ℕ → List Variation → ℕ
count-aux acc [] = acc
count-aux acc (increased ∷ l) = count-aux (1 + acc) l
count-aux acc (_ ∷ l) = count-aux acc l

count : List Variation → ℕ
count = count-aux 0

pipeline : List Sample → ℕ
pipeline = count ∘ analyze ∘ (observe memorizer2) ∘ summarize ∘ (observe memorizer3)

test4 : pipeline ex1 ≡ 0
test4 = refl

-- IO

open import Level
open import IO
open import Data.String using (String; _++_; lines)
open import Data.Maybe hiding (_>>=_) renaming (map to mapₘ)
open import Data.Nat.Show
open import Data.Unit.Polymorphic

traverse : ∀ {A : Set} → List (Maybe A) → Maybe (List A)
traverse [] = just []
traverse (just x ∷ l) with traverse l
... | just l' = just (x ∷ l')
... | nothing = nothing
traverse (nothing ∷ l) = nothing

showCount : Maybe ℕ → IO {0ℓ} ⊤
showCount (just c) = putStrLn $ show c
showCount nothing = putStrLn "error"

main : Main
main = run do
  content ← readFiniteFile "input-p2"
  let ls = lines content
  let parsed = traverse $ mapₗ (readMaybe 10) ls -- Maybe (List ℕ)
  let count = mapₘ pipeline parsed
  showCount count
