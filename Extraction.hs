{-# LANGUAGE DeriveDataTypeable, GADTs, ScopedTypeVariables #-}
module Extraction where

import Data.Maybe
import Data.Char
import Data.Bits
import Data.Typeable

--boolrec t f b = if b then t b else f b

__ :: ()
__ = Prelude.error "Logical or arity value used"

stringrec :: ([Char] -> a) -> (Char -> [Char] -> a) -> [Char] -> a
stringrec n c l = case l of
                    [] -> n []
                    (b : bs) -> c b bs

sumboolrec :: (() -> a) -> (() -> a) -> Bool -> a
sumboolrec t f b = if b then t __ else f __

sumorrec :: (a -> b) -> (() -> b) -> Maybe a -> b
sumorrec f f0 s = case s of
                    Just x -> f x
                    Nothing -> f0 __

prodrec :: (a -> b -> c) -> (a, b) -> c
prodrec f (a, b) = f a b

natrec :: (Int -> a) -> (Int -> a) -> Int -> a
natrec z s 0 = z 0
natrec z s n = s (n - 1)

natinc :: Int -> Int
natinc n = n + 1
natminus :: Int -> Int -> Int
natminus a b = max 0 $ a - b

-- lt_eq_lt_dec :: Prelude.Int -> Prelude.Int -> Sumor Sumbool
-- lt_eq_lt_dec n m =
--   nat_rec (\m0 ->
--     ( let r z s n = case n of {0 -> z 0 ; q -> s (q Prelude.- 1)} in r )
--       (\_ -> Inleft
--       Right)
--       (\m1 -> Inleft
--       Left)
--       m0) (\n0 iHn m0 ->
--     ( let r z s n = case n of {0 -> z 0 ; q -> s (q Prelude.- 1)} in r )
--       (\_ ->
--       Inright)
--       (\m1 ->
--       iHn m1)
--       m0) n m

lt_eq_lt_dec :: Int -> Int -> Maybe Bool
lt_eq_lt_dec n m =
    if n < m then Just True
    else if n == m then Just False
         else Nothing

le_lt_dec :: Int -> Int -> Bool
le_lt_dec n m = (n <= m)

data Cmp = Eq | Lt | Gt deriving Typeable

cmprec :: (Cmp -> a) -> (Cmp -> a) -> (Cmp -> a) -> Cmp -> a
cmprec x _ _ Eq = x Eq
cmprec _ x _ Lt = x Lt
cmprec _ _ x Gt = x Gt

nat_compare :: Int -> Int -> Cmp
nat_compare n m =
    if n < m then Lt
       else if n > m then Gt
            else Eq

eq_nat_dec :: Int -> Int -> Bool
eq_nat_dec = (==)

makechar :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Char
makechar x8 x7 x6 x5 x4 x3 x2 x1 = chr
                                   (foldl (\ acc b -> acc * 2 +
                                                      if b then 1 else 0) 0
                                    [x1, x2, x3, x4, x5, x6, x7, x8])

charrec :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> a) -> Char -> a
charrec f c =
    let o = ord c
        m = testBit o
    in f (m 0) (m 1) (m 2) (m 3) (m 4) (m 5) (m 6) (m 7)

type Fin = (Int, Int)

fin1 :: Int -> Fin
fin1 n = (0, n + 1)

fins :: Int -> Fin -> Fin
fins _ (m, n) = (m + 1, n + 1)

finrec :: (Int -> a) -> (Int -> Fin -> a) -> Fin -> a
finrec f f0 (m, o) =
    if m == 0
    then f o
    else f0 o (m-1, o-1)

type Vec a = (Int, [a]) -- length, contents

vecNil :: Vec a
vecNil = (0, [])

vecCons :: a -> Int -> Vec a -> Vec a
vecCons a _ (n, b) = (n + 1, a : b)

vecRec :: (Int -> b) -> (a -> Int -> Vec a -> b) -> Vec a -> b
vecRec b _ (0, _) = (b 0)
vecRec _ r (n, (x : l)) = r x n (n-1, l)
