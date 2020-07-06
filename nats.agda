module nats where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

three : Nat
three = succ 2 -- The pragma lets us use literals like '2'

_+_ : Nat -> Nat -> Nat
zero + n = n
(succ m) + n = succ (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    (succ (succ zero)) + (succ (succ (succ zero)))
  ≡⟨⟩
    succ ((succ zero) + (succ (succ (succ zero))))
  ≡⟨⟩
    succ (succ (zero + (succ (succ (succ zero)))))
  ≡⟨⟩
    succ (succ (succ (succ (succ zero))))
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    (succ (succ (succ zero)) + (succ (succ (succ (succ zero)))))
  ≡⟨⟩
    succ (succ (succ zero) + (succ (succ (succ (succ zero)))))
  ≡⟨⟩
    succ (succ ((succ zero) + (succ (succ (succ (succ zero))))))
  ≡⟨⟩
    succ (succ (succ (zero + (succ (succ (succ (succ zero)))))))
  ≡⟨⟩
    succ (succ (succ (succ (succ (succ (succ zero))))))
  ≡⟨⟩
    7
  ∎

_*_  : Nat -> Nat -> Nat
0 * n = 0 -- Base case
(succ m) * n = n + (m * n) -- Inductive step

-- Proof that 2 * 3 = 6
_ =
  begin
    2 * 3
  ≡⟨⟩
    (succ 1) * 3 -- True by definition of 2
  ≡⟨⟩
    3 + (1 * 3) -- True by inductive step
  ≡⟨⟩
    3 + ((succ 0) * 3) -- True by definition of 1
  ≡⟨⟩
    3 + (3 + (0 * 3)) -- True by inductive step
  ≡⟨⟩
    3 + (3 + 0) -- True by base case
  ≡⟨⟩
    3 + 3 -- True by addition
  ≡⟨⟩
    6 -- True by addition
  ∎

-- Definition of exponentiation
_^_ : Nat -> Nat -> Nat
n ^ 0 = 1
n ^ (succ m) = n * (n ^ m)

-- Proof that 3 ^ 4 = 81 according to our definition
-- of ^
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    81
  ∎

-- Definition of monus: it's minus but x - y = 0 when y > x.
_∸_ : Nat -> Nat -> Nat
m ∸ zero = m
zero ∸ (succ n) = zero
(succ m) ∸ (succ n) = m ∸ n

-- Proof that 5 ∸ 3 = 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

-- Proof that 3 ∸ 5 = 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

-- Specifying precedence levels
infixl 6 _+_ _∸_
infixl 7 _*_

-- These say that our operators correspond to the ones in Haskell
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin

inc : Bin -> Bin
inc ⟨⟩ = ⟨⟩
inc (⟨⟩ O) = ⟨⟩ I
inc (⟨⟩ I) = ⟨⟩ I O
inc (b O)  = b I
inc (b I)  = (inc b) O

-- Proof that inc O = I
_ =
  begin
    inc (⟨⟩ O)
  ≡⟨⟩  
   ⟨⟩ I -- True by definition
  ∎

-- Proof that inc I = I 0
_ =
  begin
    inc (⟨⟩ I)
  ≡⟨⟩
    ⟨⟩ I O -- By definition
  ∎

-- Proof that inc I 0 = I I
_ =
  begin
    inc (⟨⟩ I O)
  ≡⟨⟩
    ⟨⟩ I I -- By definition
  ∎

-- Proof that inc I I = I O O
_ =
  begin
    inc (⟨⟩ I I)
  ≡⟨⟩
    (inc (⟨⟩ I)) O -- By fourth rule in defintiion
  ≡⟨⟩
    ⟨⟩ I O O -- By second rule in defintion
  ∎

-- Define operator to convert decimal to binary
to : Nat -> Bin
to zero = ⟨⟩ O
to (succ n) = inc (to n)

-- Proof that (to 1) = ⟨⟩ I
_ =
  begin
    to 1
  ≡⟨⟩
    to (succ 0) -- By definition of 1
  ≡⟨⟩
    inc (to 0) -- By inductive definition of to
  ≡⟨⟩
    inc (⟨⟩ O)
  ≡⟨⟩
    ⟨⟩ I
  ∎

-- Proof that (to 2) = ⟨⟩ I 0
_ =
  begin
    to 2
  ≡⟨⟩
    to (succ 1) -- By definition of 2
  ≡⟨⟩
    inc (to 1) -- By inductive def of to
  ≡⟨⟩
    inc (⟨⟩ I) -- See above proof
  ≡⟨⟩
    ⟨⟩ I O -- By definition of inc
  ∎

-- Proof that (to 3) = ⟨⟩ I I
_ =
  begin
    to 3
  ≡⟨⟩
    to (succ 2) -- By definition of 3
  ≡⟨⟩
    inc (to 2) -- By inductive def of to
  ≡⟨⟩
    inc (⟨⟩ I O)
  ≡⟨⟩
    ⟨⟩ I I
  ∎

-- Defines a function to convert from binary nums to natural nums
from : Bin -> Nat
from ⟨⟩ = zero
from (⟨⟩ O) = zero
from (⟨⟩ I) = 1
from (b O) = 2 * (from b)
from (b I) = 2 * (from b) + 1

-- Proof that from I O = 2
_ =
  begin
   from (⟨⟩ I O)
  ≡⟨⟩
    2 * (from (⟨⟩ I))
  ≡⟨⟩
    2 * 1
  ≡⟨⟩
    2
  ∎

-- Proof that I I = 3
_ =
  begin
    from(⟨⟩ I I)
  ≡⟨⟩
    2 * from(⟨⟩ I) + 1
  ≡⟨⟩
    2 * 1 + 1
  ≡⟨⟩
    2 + 1
  ≡⟨⟩
    3
  ∎

-- Proof that I O O = 4
_ =
  begin
    from(⟨⟩ I O O)
  ≡⟨⟩
    2 * from(⟨⟩ I O)
  ≡⟨⟩
    2 * 2
  ≡⟨⟩
    4
  ∎
