
{-# OPTIONS --guardedness #-}

module aoc-03-p2 where

open import Data.Bool hiding (_≤?_ ; _≤_ ; _<_)
open import Data.Product hiding (swap)
open import Function
open import Data.Fin hiding (_≤_ ; Ordering ; compare ; _<_)
open import Data.Nat
open import Data.Nat.Show
open import Data.String hiding (show ; _≤_ ; _<_)
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
  Position = Σ[ n ∈ ℕ ] n Data.Nat.< L

  toFin : Position → Fin L
  toFin (n , p) = fromℕ< p

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

module Parser (L : ℕ) where
  open Model L

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

  parseWord : String → Maybe Word
  parseWord str = (str |> chars |> bits) >>= mkWord

  traverse : List (Maybe Word) → Maybe Sequence
  traverse [] = just []
  traverse (x ∷ l) = x >>= λ h → traverse l >>= λ t → just (h ∷ t)

  parse : List String → Maybe Sequence
  parse l = l |> mapₗ parseWord |> traverse

ex1 : List String
ex1 = "010101"
    ∷ "111000"
    ∷ "000111"
    ∷ "001100"
    ∷ "101101"
    ∷ "001110" ∷ []
mseq1 = Parser.parse 6 ex1

module Filter (L : ℕ) where
  open Model L

  single-pass : Position → Bit → Sequence → Sequence
  single-pass pos bit [] = []
  single-pass pos bit (x ∷ s) with bit Data.Bool.≟ (lookup x (toFin pos))
  ... | false because proof₁ = single-pass pos bit s
  ... | true because proof₁ = x ∷ single-pass pos bit s

  suc-asc : ∀ (n : ℕ) → n ≤ suc n
  suc-asc zero = z≤n
  suc-asc (suc n) = s≤s (suc-asc n)

  lem0 : ∀ {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
  lem0 {zero} ab bc = z≤n 
  lem0 {suc a} {suc b} {suc c} (s≤s ab) (s≤s bc) = s≤s (lem0 ab bc)

  lem1 : ∀ {l : ℕ} → suc l < L → l < L
  lem1 {zero} (s≤s sl<L) = s≤s z≤n
  lem1 {suc l} (s≤s sl<L) = s≤s (lem0 (suc-asc (suc l)) sl<L)

  multi-pass : Position → Bit → Sequence → Maybe Sequence
  multi-pass pos bit s with single-pass pos bit s
  ... | [] = nothing
  ... | x ∷ [] = just Data.List.[ x ]
  multi-pass (zero , p) bit s | x ∷ x₁ ∷ s' = nothing
  multi-pass (suc l , p) bit s | x ∷ x₁ ∷ s' = multi-pass (l , lem1 p) bit (x ∷ x₁ ∷ s')
