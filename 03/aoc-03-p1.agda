{-# OPTIONS --guardedness #-}

module aoc-03-p1 where

open import Data.Nat
open import Data.Bool hiding (_≤?_)
open import Data.Product hiding (swap)
open import Function
open import Data.Nat.Show
open import Data.String hiding (show)
open import Data.Maybe hiding (zip) renaming (map to mapₘ)
open import Data.List hiding (zip) renaming (map to mapₗ ; length to lengthₗ)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Vec hiding (toList ; foldr ; _>>=_) renaming (map to v-map ; zip to v-zip ; foldl to v-foldl)

-- MODEL


module Model (L : ℕ) where
  neg : ℕ → ℕ
  neg 0 = 1
  neg 1 = 0
  neg n = n

  Word : Set
  Word = Vec ℕ L

  BiWord : Set
  BiWord = Vec (ℕ × ℕ) L

  w-map : (ℕ → ℕ) → Word → Word
  w-map f w = v-map f w

  w-bimap : (ℕ → ℕ → ℕ) → BiWord → Word
  w-bimap f bw = v-map (uncurry f) bw

  w-add : Word → Word → Word
  w-add w1 w2 = w-bimap (_+_) $ v-zip w1 w2

  w-neg : Word → Word
  w-neg = w-map neg

  State : Set
  State = Word × Word

  state : Word → State
  state w = w , w-neg w

  exec : State → Word → State
  exec (s , ¬s) w = w-add s w , w-add ¬s (w-neg w)

  w-zero : (l : ℕ) → Vec ℕ l
  w-zero zero = []
  w-zero (suc l) = 0 ∷ w-zero l

  start : State
  start = w-zero L , w-neg (w-zero L)

  run : State → List Word → State
  run = foldl exec

  cmp : ℕ → ℕ → ℕ
  cmp a b with a ≤? b
  ... | false because proof₁ = 1
  ... | true because proof₁ = 0

  gamma : State → Word
  gamma (w1 , w2) = let z = v-zip w1 w2
                    in w-bimap cmp z

  epsilon : State → Word
  epsilon = w-neg ∘ gamma

  decimal : ∀ {l : ℕ} → Vec ℕ l → ℕ
  decimal {l} v = v-foldl (λ n → ℕ) (λ acc b → 2 * acc + b) 0 v

  eval : State → ℕ
  eval s = decimal (gamma s) * decimal (epsilon s)


  -- -- PARSER

  chars : String → List String
  chars str = mapₗ fromChar $ toList str

  ints : List String → Maybe (List ℕ)
  ints [] = just []
  ints (x ∷ l) = do
          h ← readMaybe 10 x
          t ← ints l
          just $ h ∷ t

  take-to-vec : (n : ℕ) → List ℕ → Maybe (Vec ℕ n)
  take-to-vec zero l = just []
  take-to-vec (suc n) [] = nothing
  take-to-vec (suc n) (x ∷ l) = take-to-vec n l >>= λ t → just (x ∷ t)

  mkWord : List ℕ → Maybe Word
  mkWord l = take-to-vec L l

  parse : String → Maybe Word
  parse str = (str |> chars |> ints) >>= mkWord

  traverse : List (Maybe Word) → Maybe (List Word)
  traverse [] = just []
  traverse (x ∷ l) = x >>= λ h → traverse l >>= λ t → just (h ∷ t)

  process : List String → Maybe State
  process l = mapₗ parse l |> traverse |> mapₘ (run start)

-- -- EXAMPLE

ex1 : List String
ex1 = "00100"
    ∷ "11110"
    ∷ "10110"
    ∷ "10111"
    ∷ "10101"
    ∷ "01111"
    ∷ "00111"
    ∷ "11100"
    ∷ "10000"
    ∷ "11001"
    ∷ "00010"
    ∷ "01010" ∷ []

run1 : Maybe (Model.State 5)
run1 = (Model.process 5) ex1

_ : mapₘ (Model.eval 5) run1 ≡ just 198
_ = refl

-- IO

open import Level
open import IO renaming (run to runIO)
open import Data.Unit.Polymorphic

showResult : Maybe ℕ → IO {0ℓ} ⊤
showResult (just x) = putStrLn $ show x
showResult nothing = putStrLn "error"

main : Main
main = runIO $
   readFiniteFile "input-p1"
   IO.>>= λ content → let lines = words content
                          counts = (Model.process 12) lines
                      in showResult $ mapₘ (Model.eval 12) counts
