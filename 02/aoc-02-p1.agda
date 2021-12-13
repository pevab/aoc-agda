{-# OPTIONS --guardedness #-}

module aoc-02-p1 where

open import Data.Bool
open import Data.Nat
open import Data.Nat.Show
open import Data.Maybe renaming (map to mapₘ)
open import Data.List using (List ; _∷_ ; foldl ; [_] ; [] ) renaming (map to mapₗ)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Function

-- MACHINE

record Position : Set where
  constructor position
  field
    length : ℕ
    depth : ℕ

origin : Position
origin = position 0 0

data Instruction : Set where
  forward : ℕ → Instruction
  down : ℕ → Instruction
  up : ℕ → Instruction

Program : Set
Program = List Instruction

step : Position → Instruction → Position
step (position length depth) (forward x) = position (x + length) depth
step (position length depth) (down x) = position length (x + depth)
step p (up zero) = p
step (position length zero) (up (suc x)) = position length zero
step (position length (suc depth)) (up (suc x)) = step (position length depth) (up x)

exec : Program → Position → Position
exec prog p = foldl step p prog

prog0 = (forward 5)
      ∷ (down 5)
      ∷ (forward 8)
      ∷ (up 3)
      ∷ (down 8)
      ∷ ( forward 2 ) ∷ []
test0 : exec prog0 origin ≡ position 15 10
test0 = refl

-- PARSER

open import Data.String hiding (show)

data Token : Set where
  FORWARD : Token
  DOWN : Token
  UP : Token
  VALUE : String → Token

keywords : List (String × Token)
keywords = ( "forward" , FORWARD )
         ∷ ( "down" , DOWN )
         ∷ ( "up" , UP )
         ∷ []

tokenize-aux : List (String × Token) → (String → Token) → String → Token
tokenize-aux [] default s = default s
tokenize-aux ((kw , token) ∷ kws) default s = if s == kw then token else tokenize-aux kws default s

tokenize : String → Token
tokenize = tokenize-aux keywords VALUE

lex : String → List Token
lex = mapₗ tokenize ∘ words

input1 : String
input1 = "forward 4
down 3
up 2 forward 1"

sem : List Token → Maybe Program
sem [] = just []
sem (x ∷ []) = nothing
sem (FORWARD ∷ (VALUE x) ∷ l) = do
  n ← readMaybe 10 x
  p ← sem l
  just $ forward n ∷ p
sem (FORWARD ∷ _ ∷ l) = nothing
sem (DOWN ∷ (VALUE x) ∷ l) = do
  n ← readMaybe 10 x
  p ← sem l
  just $ down n ∷ p
sem (DOWN ∷ _ ∷ l) = nothing
sem (UP ∷ (VALUE x) ∷ l) = do
  n ← readMaybe 10 x
  p ← sem l
  just $ up n ∷ p
sem (UP ∷ _ ∷ l) = nothing
sem (VALUE x ∷ l) = nothing

parse : String → Maybe Program
parse = sem ∘ lex

-- IO

open import Level
open import IO
open import Data.Unit.Polymorphic

showResult : Maybe Position → IO {0ℓ} ⊤
showResult (just (position l d)) = putStrLn $ show (l * d)
showResult nothing = putStrLn "error"

main : Main
main = run $
  readFiniteFile "input-p1"
  IO.>>= λ content → let progₘ = parse content
                         machineₘ = mapₘ exec progₘ
                         posₘ = mapₘ (λ machine → machine origin) machineₘ
                      in showResult posₘ
