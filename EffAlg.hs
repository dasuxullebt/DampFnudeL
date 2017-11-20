module Main where
import Data.Char
import qualified Data.ByteString as BS
import Data.Word
import Data.Bits
import System.Environment
import Prelude hiding (lookup)
import DecompressHelper hiding (mainWithArgs)

import qualified NoRBR
import qualified Extraction

import System.IO
import qualified System.Environment

-- Pairing Heap

data Pheap a = Empty | Heap a [Pheap a]

findmin :: Ord a => Pheap a -> Maybe a
findmin Empty = Nothing
findmin (Heap x _) = Just x

merge :: Ord a => Pheap a -> Pheap a -> Pheap a
merge Empty x = x
merge x Empty = x
merge w@(Heap x xs) z@(Heap y ys) =
    if (x < y)
    then Heap x (z : xs)
    else Heap y (w : ys)

insert :: Ord a => a -> Pheap a -> Pheap a
insert x h = merge (Heap x []) h

mergepairs :: Ord a => [Pheap a] -> Pheap a
mergepairs [] = Empty
mergepairs (Empty : r) = mergepairs r
mergepairs (x : []) = x
mergepairs (x : y : r) = merge (merge x y) (mergepairs r)

deletemin :: Ord a => Pheap a -> Pheap a
deletemin Empty = Empty
deletemin (Heap x xs) = mergepairs xs

segment' :: Ord a => a -> [a] -> Pheap a -> ([a], Pheap a)
segment' x l r =
    case findmin r of
      Nothing -> (l, r)
      Just y -> if y <= x
                then segment' x (y : l) (deletemin r)
                else (l, r)

segment :: Ord a => a -> Pheap a -> ([a], Pheap a)
segment x r =
    let (k, h) = segment' x [] r
    in (reverse k, h)

bulk_insert :: Ord a => [a] -> Pheap a -> Pheap a
bulk_insert [] r = r
bulk_insert (x : l) r = bulk_insert l (insert x r)
       
type SWBR1 a = [Either a Int]

transform :: NoRBR.SequenceWithBackRefs a -> SWBR1 a
transform [] = []
transform (Left a : r) = Left a : transform r
transform (Right (0, _) : r) = transform r
transform (Right (n, d) : r) = Right d : transform (Right (n-1, d) : r)

maxDist :: Int
maxDist = 32768
                               
data RState a = RState
    { n :: Int
    , ln :: SWBR1 a
    , m :: Int
    , lm :: SWBR1 a
    , b :: Pheap (Int, Int)
    , c :: Pheap (Int, a) }

rs_start :: SWBR1 a -> RState a
rs_start s = RState
             { n = 0
             , ln = s
             , m = 0
             , lm = s
             , b = Empty
             , c = Empty }

m_inc :: Ord a => RState a -> RState a
m_inc r =
    let h = head $ lm r
    in RState
           { n = n r
           , ln = ln r
           , m = m r + 1
           , lm = tail $ lm r
           , b = case h of
                   Left _ -> b r
                   Right k -> insert (m r - k, m r) (b r)
           , c = c r }
      
n_inc :: Ord a => RState a -> (a, RState a)
n_inc r =
    let (h, c2) = case head $ ln r of
                    Left a -> (a, c r)
                    Right n -> case findmin (c r) of
                                 Just (_ , a) -> (a, deletemin (c r))
        (b_seg, b2) = segment (n r, maxBound :: Int) $ b r
        mp (_, y) = (y, h)
        b_seg_mp = map mp b_seg
        c3 = bulk_insert b_seg_mp c2
    in (h, RState
             { n = n r + 1
             , ln = tail $ ln r
             , m = m r
             , lm = lm r
             , b = b2
             , c = c3 })

maybe_proceed :: Ord a =>
                 RState a ->
                 Maybe (a, RState a)
maybe_proceed r =
    if ln r == []
    then Nothing
    else if (m r - n r <= maxDist) && (lm r /= [])
         then maybe_proceed $ m_inc r
         else Just $ n_inc r
                
resolve' :: Ord a => RState a -> [a]
resolve' r = case maybe_proceed r of
               Nothing -> []
               Just (c, st) -> c : resolve' st

resolve :: Ord a => NoRBR.SequenceWithBackRefs a -> [a]
resolve = resolve' . rs_start . transform

convert' :: Either (Extraction.Vec Prelude.Bool) (Int, Int) ->
            Either Word8 (Int, Int)
convert' (Left v) = Left $ convertbyte $ convertvec v
convert' (Right b) = Right b
          
convert :: (NoRBR.SequenceWithBackRefs (Extraction.Vec Prelude.Bool)) ->
           NoRBR.SequenceWithBackRefs Word8
convert = map convert'
                
-- Actual Extraction


mainWithArgs :: [String] -> IO ()
mainWithArgs args = do
  content <- BS.readFile (head args)
  let unc = NoRBR.deflateNoRBR
            (bytesToBits (gzStrip (BS.unpack content)))
  case unc of
    Left result -> do BS.writeFile (args !! 1)
                            (BS.pack $ resolve $ convert result)
    Right error -> do putStrLn error
            
main :: IO ()
main = do
  args <- System.Environment.getArgs
  mainWithArgs args
