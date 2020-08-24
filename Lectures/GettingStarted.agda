module Lectures.GettingStarted where

-- This is a comment

{- And this is a multiline comment.

   Useful key-bindings:

   C-c C-l     load file

 -}

const : {A B : Set} -> A -> B -> A
const = λ a b -> a

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

append : {A : Set} -> List A -> List A -> List A
append [] ys = ys
append (x :: xs) ys = x :: (append xs ys)
