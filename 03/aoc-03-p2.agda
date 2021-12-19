
{-# OPTIONS --guardedness #-}

module aoc-03-p2 where

open import Data.Bool hiding (_≤?_ ; _≤_)
open import Data.Product hiding (swap)
open import Function
open import Data.Fin hiding (_≤_ ; Ordering ; compare)
open import Data.Nat
open import Data.Nat.Show
open import Data.String hiding (show ; _≤_)
open import Data.Maybe hiding (zip) renaming (map to mapₘ)
open import Data.List hiding (zip ; lookup) renaming (map to mapₗ ; length to lengthₗ)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Vec hiding (toList ; foldr ; _>>=_) renaming (map to v-map ; zip to v-zip ; foldl to v-foldl)
open import Data.Unit.Polymorphic

-- MODEL

module Model (L : ℕ) where
  Bit : Set
  Bit = Bool
  0♭ : Bit
  0♭ = false
  1♭ : Bit
  1♭ = true

  Word : Set
  Word = Vec Bit L

  Count : Set
  Count = Vec ℕ L

  w-add : ∀ {l} → Vec ℕ l → Vec Bit l → Vec ℕ l
  w-add [] [] = []
  w-add (n ∷ ns) (b ∷ bs) = let n′ = if b then (suc n) else n
                            in n′ ∷ (w-add ns bs)

  w-not : Word → Word
  w-not = v-map not

  c-add : Count → Word → Count
  c-add = w-add {L}

  c-anti-add : Count → Word → Count
  c-anti-add c w = w-add {L} c (v-map not w)

  Position : Set
  Position = Fin L

  Sequence : Set
  Sequence = List Word

  c-zero : ∀ {l} → Vec ℕ l
  c-zero {zero} = []
  c-zero {suc l} = 0 ∷ c-zero

  countOnes : Sequence → Count
  countOnes = foldl c-add c-zero

  countZeroes : Sequence → Count
  countZeroes = foldl c-anti-add c-zero

  countBoth : Sequence → Count × Count
  countBoth s = (countZeroes s) , (countOnes s)

  module Parser where

    chars : String → List String
    chars str = mapₗ fromChar $ toList str

    even♭ : ℕ → Bit
    even♭ zero = 0♭
    even♭ (suc zero) = 1♭
    even♭ (suc (suc n)) = even♭ n

    bits : List String → Maybe (List Bit)
    bits [] = just []
    bits (x ∷ l) = do
            h ← readMaybe 10 x
            t ← bits l
            just $ even♭ h ∷ t

    take-to-vec : (n : ℕ) → List Bit → Maybe (Vec Bit n)
    take-to-vec zero l = just []
    take-to-vec (suc n) [] = nothing
    take-to-vec (suc n) (x ∷ l) = take-to-vec n l >>= λ t → just (x ∷ t)

    mkWord : List Bit → Maybe Word
    mkWord l = take-to-vec L l

    parse : String → Maybe Word
    parse str = (str |> chars |> bits) >>= mkWord

    traverse : List (Maybe Word) → Maybe (List Word)
    traverse [] = just []
    traverse (x ∷ l) = x >>= λ h → traverse l >>= λ t → just (h ∷ t)

  Cmp : Set
  Cmp = Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] Ordering m n

  cmp : ∀ {l} → (Vec ℕ l) × (Vec ℕ l) → Vec Cmp l
  cmp {zero} ([] , []) = []
  cmp {suc l} (x₀ ∷ c₀ , x₁ ∷ c₁) = (x₀ , x₁ , compare x₀ x₁) ∷ cmp (c₀ , c₁)

  Mask : Set
  Mask = Vec Cmp L

  makeMask : Sequence → Mask
  makeMask = cmp ∘ countBoth

  data Subsingleton {A : Set} : A → Set where
    empty : ∀ {a : A} → Subsingleton a
    singleton : (a : A) → Subsingleton a

  BitCriteria : Set
  BitCriteria = Position → (w : Word) → Subsingleton w

  mkCriteria-aux : Bit → Cmp → Bit → (w : Word) → Subsingleton w
  mkCriteria-aux tie (c₀ , .(suc (c₀ Data.Nat.+ k)) , less .c₀ k) bit w = if bit then singleton w else empty
  mkCriteria-aux tie (c₀ , .c₀ , equal .c₀) bit w = if bit ∧ tie then singleton w else empty
  mkCriteria-aux tie (.(suc (c₁ Data.Nat.+ k)) , c₁ , greater .c₁ k) bit w = if bit then empty else singleton w

  makeCriteria : Bit → Mask → BitCriteria
  makeCriteria tie mask pos w = mkCriteria-aux tie (lookup mask pos) (lookup w pos) w

  mostCommon : Mask → BitCriteria
  mostCommon = makeCriteria 1♭

  leastCommon : Mask → BitCriteria
  leastCommon = makeCriteria 0♭

  singlePass : Position → BitCriteria → Sequence → Sequence
  singlePass pos criteria [] = []
  singlePass pos criteria (w ∷ s) with criteria pos w
  ... | empty = singlePass pos criteria s
  ... | singleton .w = w ∷ (singlePass pos criteria s)

