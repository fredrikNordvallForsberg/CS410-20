module Lectures.LineNumbers where

open import Data.Nat
open import Data.Nat.Show as NS
open import Data.String as String
open import Data.List as List
open import Data.Product
open import Data.Unit

open import Codata.Musical.Costring using (toCostring)

---------------------------------------------------------------------------
-- The IO monad
--------------------------------------------------------------------------

open import IO.Primitive

postulate
  lines : String -> List String

{-# COMPILE GHC lines = Data.Text.lines #-}

main : IO ⊤
main = do
  f ← readFiniteFile "LineNumbers.agda"
  let lf = lines f
  let nlf = List.map (λ (n , l) → NS.show n String.++ ": " String.++ l) (List.zip (List.map suc (upTo (List.length lf))) lf)
  putStrLn (toCostring (unlines nlf))

