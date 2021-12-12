{-# OPTIONS --guardedness #-}

module aoc-01-p1 where

open import Data.Nat
open import Data.Bool hiding (_<_)
open import Data.List renaming (map to mapₗ)
open import Data.Maybe hiding (_>>=_) renaming (map to mapₘ)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function

Sample : Set
Sample = ℕ

record Observation (D : Set) : Set where
  constructor observation
  field
    datum : D
    sample : Sample

observer : List (Observation (Maybe Sample)) → Sample → List (Observation (Maybe Sample))
observer [] s = [ observation nothing s ]
observer (x ∷ l) s = observation (just $ Observation.sample x) s ∷ x ∷ l

observe : List Sample → List (Observation (Maybe Sample))
observe l = reverse $ foldl observer [] l

ex1 : List Sample
ex1 = 200 ∷ 201 ∷ 201 ∷ [ 200 ]

obs1 = (observation nothing 200)
            ∷ (observation (just 200) 201)
            ∷ (observation (just 201) 201)
            ∷ [ observation (just 201) 200 ]
test1 : observe ex1 ≡ obs1
test1 = refl

data Variation : Set where
  na : Variation
  increased : Variation
  decreased : Variation
  equal : Variation

analyzer : Observation (Maybe Sample) → Observation Variation
analyzer (observation (just previous) sample) = if previous <ᵇ sample
                                                then observation increased sample
                                                else ( if sample <ᵇ previous
                                                       then observation decreased sample
                                                       else observation equal sample )
analyzer (observation nothing sample) = observation na sample

analyze : List  (Observation (Maybe Sample)) → List (Observation Variation)
analyze = mapₗ analyzer

an1 = (observation na 200)
      ∷ (observation increased 201)
      ∷ (observation equal 201)
      ∷ [ observation decreased 200 ]
test2 : (analyze ∘ observe) ex1 ≡ an1
test2 = refl

count-aux : ℕ → List (Observation Variation) → ℕ
count-aux acc [] = acc
count-aux acc (observation increased sample ∷ l) = count-aux (1 + acc) l
count-aux acc (observation _ sample ∷ l) = count-aux acc l

count : List (Observation Variation) → ℕ
count = count-aux 0

test3 : (count ∘ analyze ∘ observe) ex1 ≡ 1
test3 = refl

open import Level
open import IO
open import Data.String using (String; _++_; lines)
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
  content ← readFiniteFile "input"
  let ls = lines content
  let parsed = traverse $ mapₗ (readMaybe 10) ls -- Maybe (List ℕ)
  let count = mapₘ (count ∘ analyze ∘ observe) parsed
  showCount count
