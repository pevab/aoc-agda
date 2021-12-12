{-# OPTIONS --guardedness #-}

module aoc-01 where

open import Level
open import Data.Nat.Base
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_; lines)
open import Data.Unit.Polymorphic
open import IO

main : Main
main = run do
  line ← getLine
  putStrLn line
