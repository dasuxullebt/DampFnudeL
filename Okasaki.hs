{-# LANGUAGE DeriveDataTypeable, GADTs, ScopedTypeVariables #-}
module Okasaki where

import Control.Exception.Base
import Data.Maybe
import Data.Word
import Data.Bits
import Unsafe.Coerce
import Data.Typeable

b2i True = 1
b2i False = 0

data XList b where
    Nil :: List b
    Cons :: b -> List b -> List b
    BCons :: Word8 -> Word64 -> List Bool -> List Bool

type List b = (b -> XList b -> XList b, List b)

instance Show b => Show (List b) where
    -- show = show . listToHaskellList
    show Nil = "[]"
    show (Cons b l) = (show b) ++ "-" ++ show l
    show (BCons w8 w16 l) = "[" ++ (show w8) ++ "," ++ (show w16) ++ "]-" ++ show l

cons :: Typeable b => b -> List b -> List b
cons bc l = case cast bc of
             Just (b :: Bool) -> (unsafeCoerce (cons_ b ((unsafeCoerce l) :: List Bool))) :: List b
             Nothing -> Cons bc l

{-# RULES "cons/Bool" cons = cons_ #-}
cons_ :: Bool -> List Bool -> List Bool
cons_ b l@(BCons n bits r) = if n == 63
                             then BCons 0 (b2i b) l
                             else BCons (n + 1) ((shiftL bits 1) + b2i b) r
cons_ b Nil = BCons 0 (b2i b) Nil
cons_ b (Cons c r) = BCons 1 (b2i b + 2 * b2i c) r
                     
destruct :: Typeable b => List b -> Maybe (b, List b)
destruct Nil = Nothing
destruct (Cons b c) = Just (b, c)
destruct (BCons n bits r) = Just (testBit bits 0,
                                          if n == 0
                                          then r
                                          else BCons (n - 1) (shiftR bits 1) r)

listToHaskellList :: Typeable b => List b -> [b]
listToHaskellList l = case destruct l of
                        Nothing -> []
                        Just (x, y) -> x : listToHaskellList y

haskellListToList :: Typeable b => [b] -> List b
haskellListToList [] = Nil
haskellListToList (b : l) = cons b (haskellListToList l)

splice :: Typeable a => Int -> List a -> (List a, List a)
splice len b =
    let (l, r) = splitAt (len `div` 2) $ listToHaskellList b
    in (haskellListToList l, haskellListToList $ reverse r)

data Queue a = Queue {qLength :: Int, leftList :: List a, rightList :: List a} deriving (Show, Typeable)

qEmpty :: Typeable a => Queue a
qEmpty = Queue {qLength = 0, leftList = Nil, rightList = Nil}

qSizeIsTwo :: Typeable a => Queue a -> Bool
qSizeIsTwo q = (qLength q == 2)

qIsEmpty :: Queue a -> Bool
qIsEmpty a = (qLength a == 0)

qSlowConcat a b = if qIsEmpty a
                  then b
                  else if qIsEmpty b
                       then a
                       else let (ahd, atl) = qPopLeft a
                                (btl, bhd) = qPopRight b
                            in qPushLeft ahd (qPushRight (qSlowConcat atl btl) bhd)

-- :3
qreverse :: Typeable a => Queue a -> Queue a
qreverse a = Queue {qLength = qLength a, leftList = rightList a, rightList = leftList a}

qPushLeft :: Typeable a => a -> Queue a -> Queue a
qPushLeft a q = Queue {qLength = qLength q + 1, leftList = cons a (leftList q), rightList = rightList q}

qPushRight :: Typeable a => Queue a -> a -> Queue a
qPushRight q a = Queue {qLength = qLength q + 1, rightList = cons a (rightList q), leftList = leftList q}

qPopLeft :: Typeable a => Queue a -> (a, Queue a)
qPopLeft a = case destruct (leftList a) of
               Nothing ->
                   case destruct (rightList a) of
                     Nothing -> error "trying to read from an empty queue"
                     Just _ -> let (b, c) = splice (qLength a) (rightList a)
                               in qPopLeft (Queue {qLength = qLength a {- not a-1 -}, leftList = c, rightList = b })
               Just (x, l) -> (x, Queue {qLength = qLength a - 1, leftList = l, rightList = rightList a})

qPopRight :: Typeable a => Queue a -> (Queue a, a)
qPopRight q = let (a, r) = qPopLeft (qreverse q)
              in (qreverse r, a)

-- for testing
qPushRightList :: Typeable a => [a] -> Queue a -> Queue a
qPushRightList [] a = a
qPushRightList (b : bs) a = qPushRightList bs (qPushRight a b)

qPopLeftList :: Typeable a => Queue a -> [a]
qPopLeftList a = if qIsEmpty a
                 then []
                 else let (b, q) = qPopLeft a
                      in b : (qPopLeftList q)

test2 = qPopLeft $ qPushRightList (replicate 99 True)  qEmpty

-- result: [1, 2, 3, 4, 5, 6, 7, 8]
test :: (Typeable a, Num a) => [a]
test = qPopLeftList $ qPushRightList [1, 2, 3, 4, 5, 6, 7, 8] qEmpty

-- catenable deque
-- see http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.47.7683&rep=rep1&type=pdf

data CatDeque a = CDNode (Queue a) | CD5 (Queue a) (CatDeque (CE a)) (Queue a) (CatDeque (CE a)) (Queue a) deriving (Show, Typeable)
data CE a = CENode (Queue a) | CE3 (Queue a) (CatDeque (CE a)) (Queue a) deriving (Show, Typeable)

aCD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a1CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a2CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a3CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a4CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a5CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a6CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a7CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a8CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a9CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a10CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a11CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a12CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a13CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a14CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a15CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a16CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a17CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r
a18CD5 f a m b r = assert (qLength f >= 3) $
                 assert (qLength r >= 3) $
                 CD5 f a m b r

aCENode q = assert (qLength q >= 2) $ CENode q
aCE3 a b c = assert (qLength a >= 2) $ assert (qLength c >= 2) $ CE3 a b c

cdNil :: Typeable a => CatDeque a
cdNil = CDNode qEmpty

cdIsEmpty :: Typeable a => CatDeque a -> Bool
cdIsEmpty (CDNode x) = qIsEmpty x
cdIsEmpty (CD5 _ _ _ _ _) = False

cdCons :: Typeable a => a -> CatDeque a -> CatDeque a
cdCons x (CDNode q) = CDNode (qPushLeft x q)
cdCons x (CD5 f a m b r) = a7CD5 (qPushLeft x f) a m b r

cdSnoc :: Typeable a => CatDeque a -> a -> CatDeque a
cdSnoc (CDNode q) x = CDNode (qPushRight q x)
cdSnoc (CD5 f a m b r) x = a8CD5 f a m b (qPushRight r x)

cdLhd :: Typeable a => CatDeque a -> a
cdLhd (CDNode q) = fst (qPopLeft q)
cdLhd (CD5 f a m b r) = fst (qPopLeft f)

cdRhd :: Typeable a => CatDeque a -> a
cdRhd (CDNode q) = snd (qPopRight q)
cdRhd (CD5 f a m b r) = snd (qPopRight r)

cdLtl' :: Typeable a => CatDeque a -> CatDeque a
cdLtl' (CDNode q) = CDNode $ snd (qPopLeft q)
cdLtl' (CD5 f a m b r) = CD5 (snd $ qPopLeft f) a m b r
cdRtl' :: Typeable a => CatDeque a -> CatDeque a
cdRtl' (CDNode q) = CDNode $ fst (qPopRight q)
cdRtl' (CD5 f a m b r) = CD5 f a m b $ fst $ qPopRight r

cdConcat :: Typeable a => CatDeque a -> CatDeque a -> CatDeque a
cdConcat (CDNode q1) (CDNode q2) = if (qLength q1 < 4) || (qLength q2 < 4)
                                   then CDNode $ qSlowConcat q1 q2
                                   else let (liat1, daeh1) = qPopRight q1
                                            (head2, tail2) = qPopLeft q2
                                        in
                                           a1CD5 liat1 cdNil (qPushLeft daeh1 (qPushLeft head2 qEmpty)) cdNil tail2
cdConcat (CDNode q) (CD5 f a m b r) = if qLength q < 4
                                      then a2CD5 (qSlowConcat q f) a m b r
                                      else a3CD5 q (cdCons (CENode f) a) m b r
cdConcat (CD5 f a m b r) (CDNode d) = if qLength d < 4
                                      then a4CD5 f a m b (qSlowConcat r d)
                                      else a5CD5 f a m (cdSnoc b (CENode r)) d
cdConcat (CD5 f1 a1 m1 b1 r1_) (CD5 f2_ a2 m2 b2 r2) =
         let (r1, x) = qPopRight r1_
             (y, f2) = qPopLeft f2_
         in
            a6CD5
                f1
                (cdSnoc a1 $ aCE3 m1 b1 r1)
                (qPushLeft x (qPushLeft y qEmpty)) 
                (cdCons (aCE3 f2 a2 m2) b2)
                r2

cdLtl :: Typeable a => CatDeque a -> CatDeque a
cdLtl (CDNode d) = CDNode $ snd (qPopLeft d)
cdLtl (CD5 f a m b r) = if qLength f >= 4
                        then a9CD5 (snd $ qPopLeft f) a m b r
                        else assert (qLength f == 3) $
                         let (_, _y) = qPopLeft f
                             (y, _z) = qPopLeft _y
                             (z, _)  = qPopLeft _z
                         in if cdIsEmpty a
                            then if cdIsEmpty b
                            then cdConcat (CDNode $ qPushLeft y $ qPushLeft z $ m) $ CDNode r
                            else -- a = [], b != []
                                 assert (qLength m >= 1) $
                                 case cdLhd b of
                                  CENode d -> a10CD5 (qPushLeft y $ qPushLeft z $ m) a d (cdLtl b) r
                                  CE3 f' c' r' -> a11CD5 (qPushLeft y $ qPushLeft z $ m)
                                                      (cdCons (aCENode f') c') r' (cdLtl b) r
                            else
                                case cdLhd a of
                                     CE3 f' c' r' -> 
                                                  assert (qLength f' >= 1) $
                                                        a12CD5 (qPushLeft y $ qPushLeft z f')
                                                         (cdConcat c' (cdCons (aCENode r') (cdLtl' a))) m b r
                                     CENode d -> assert (qLength d >= 1)
                                                  a13CD5 (qPushLeft y $ qPushLeft z d) (cdLtl a) m b r

cdRtl :: Typeable a => CatDeque a -> CatDeque a
cdRtl (CDNode d) = CDNode $ fst (qPopRight d)
cdRtl (CD5 f a m b r) = if qLength r >= 4
                        then a14CD5 f a m b (fst $ qPopRight r)
                        else assert (qLength r == 3) $ 
                         let (_y, _) = qPopRight r
                             (_x, y) = qPopRight _y
                             (_,  x)  = qPopRight _x
                         in if cdIsEmpty b
                            then if cdIsEmpty a
                            then cdConcat (CDNode f) (CDNode $ qPushRight (qPushRight m x) y)
                            else -- a != [], b = []
                                 case cdRhd a of
                                  CENode d -> a15CD5 f (cdRtl a) d b (qPushRight (qPushRight m x) y)
                                  CE3 f' c' r' -> a16CD5 f (cdRtl a) f' (cdSnoc c' (aCENode r')) (qPushRight (qPushRight m x) y)
                            else
                                case cdRhd b of
                                     CE3 f' c' r' -> a17CD5 f a m (cdConcat (cdSnoc (cdRtl' b) (aCENode f')) c') (qPushRight (qPushRight r' x) y)
                                     CENode d -> a17CD5 f a m (cdRtl b) (qPushRight (qPushRight d x) y)

-- for extraction
cdRec n c l = if cdIsEmpty l
              then n l
              else c (cdLhd l) (cdLtl l)

cdReverseRec n c l = if cdIsEmpty l
                     then n l
                     else c (cdRhd l) (cdRtl l)

myResolveNthLast :: Typeable a => Int -> CatDeque a -> Either a ()
myResolveNthLast n a = if ((cdIsEmpty a) || (n < 1))
                       then Right ()
                       else if n == 1
                            then Left $ cdRhd a
                            else myResolveNthLast (n - 1) $ cdRtl a

cdOfListL :: Typeable a => [a] -> CatDeque a
cdOfListL [] = cdNil
cdOfListL (x : xs) = cdCons x $ cdOfListL xs

cdToListL :: Typeable a => CatDeque a -> [a]
cdToListL a = if cdIsEmpty a
              then []
	      else (cdLhd a) : cdToListL (cdLtl a)

cdOfListR :: Typeable a => [a] -> CatDeque a
cdOfListR [] = cdNil
cdOfListR (x : xs) = cdSnoc (cdOfListR xs) x

cdToListR :: Typeable a => CatDeque a -> [a]
cdToListR a = if cdIsEmpty a
              then []
	      else (cdRhd a) : cdToListR (cdRtl a)

-- hopefully more efficient length calculation
cdLength' :: Typeable a => Either (CatDeque a) (CE a) -> Int
cdLength' (Left (CDNode q)) = qLength q
cdLength' (Left (CD5 f a m b r)) =
    qLength f +
    foldl (+) 0 (map (cdLength' . Right) $ cdToListL a) +
    qLength m +
    foldl (+) 0 (map (cdLength' . Right) $ cdToListL b) +
    qLength r
cdLength' (Right (CENode q)) = qLength q
cdLength' (Right (CE3 a b c)) =
    qLength a +
    foldl (+) 0 (map (cdLength' . Right) $ cdToListL b) +
    qLength c

cdLength :: Typeable a => CatDeque a -> Int
cdLength = cdLength' . Left
