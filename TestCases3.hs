{-# LANGUAGE BangPatterns #-}
module Main where
import Data.Char
import qualified Data.ByteString as BS
import Data.Word
import Data.Bits
import System.Environment
import qualified Test3
import Prelude hiding (lookup)

--import qualified BackRefs
--import qualified BackRefsDiffArray as BackRefs

import System.IO
--import Data.Map ((!), Map)
import qualified System.Environment

-- remove everything except 0 and 1
rmcomments :: String -> String
rmcomments [] = []
rmcomments ('1' : r) = '1' : rmcomments r
rmcomments ('0' : r) = '0' : rmcomments r
rmcomments (_ : r) = rmcomments r

-- make boolean list
toboollist :: String -> [Bool]
toboollist = (map ('1' ==)) . rmcomments

-- convert Coq byte-list to characters
convertbyte :: [Bool] -> Word8
convertbyte l = foldl (\ acc b -> acc * 2 + if b then 1 else 0) 0 (reverse l)
--convertbyte l = foldl (\ acc b -> (shift acc 1) .|. (if b then bit 0 else 0)) 0 (reverse l)

convertbytes :: [[Bool]] -> String
convertbytes = map (\ l -> chr(foldl (\ acc b -> acc * 2 + if b then 1 else 0) 0 (reverse l)))

convertbytes2 :: [[Bool]] -> BS.ByteString
convertbytes2 = BS.pack . (map convertbyte)

tToL :: (Test3.T a) -> [a]
tToL Test3.Nil = []
tToL (Test3.Cons a _ b) = a : (tToL b)

convertbytes3 :: [Test3.T Bool] -> BS.ByteString
convertbytes3 = convertbytes2 . (map tToL)

-- to apply it to gz-file

gzStrip :: [Word8] -> [Word8]
gzStrip w8 =
  let
    untilZero :: [Word8] -> ([Word8], [Word8])
    untilZero [] = ([], [])
    untilZero (0 : l) = ([], l)
    untilZero (r : l) = let (x, y) = untilZero l in (r : x, y)
    [_ftext, fhcrc, fextra, fname, fcomment] = take 5 [0..]
    [_id1, _id2, _cm, flg, _mtime1, _mtime2, _mtime3, _mtime4, _xfl, _os] = take 10 w8
    n1 = drop 10 w8
    (n2, _extra) = if testBit flg fextra
                  then let [xl1, xl2] = map fromIntegral $ take 2 n1
                       in (drop (2 + xl1 + 256*xl2) n1, take (xl1 + 256*xl2) (drop 2 n1))
                  else (n1, [])
    (_name, n3) = if testBit flg fname then untilZero n2 else ([], n2)
    (_comment, n4) = if testBit flg fcomment then untilZero n3 else ([], n3)
    (_hcrc, n5) = if testBit flg fhcrc then (take 2 n4, drop 2 n4) else ([], n4)
    ret = take ((length n5) - 8) n5
  in ret

-- convert bytes to boolean list
intToCode :: Word8 -> [Bool]
intToCode c = map (testBit c) [0..7]

--(reverse [0..7])

bytesToBits :: [Word8] -> [Bool]
bytesToBits [] = []
bytesToBits (x : l) = (intToCode x) ++ (bytesToBits l)

--uncompress_io_result (Left x) = Left (convertbytes2 x)
--uncompress_io_result (Right x) = Right x

tBoolStr :: Test3.T Bool -> String
tBoolStr Test3.Nil = ""
tBoolStr (Test3.Cons True _ x) = "1" ++ tBoolStr x
tBoolStr (Test3.Cons False _ x) = "0" ++ tBoolStr x

--toBackRefs :: Test3.SequenceWithBackRefs (Test3.T Bool) -> BackRefs.SWBR (Test3.T Bool)
toBackRefs = id

swbrToString :: Test3.SequenceWithBackRefs (Test3.T Bool) -> String
swbrToString [] = ""
swbrToString ((Left a) : b) = "[" ++ tBoolStr a ++ "] " ++ swbrToString b
swbrToString ((Right (c, d)) : b) = "(" ++ (show c) ++ "," ++ (show d) ++ ") " ++ swbrToString b

instance Eq a => Eq (Test3.T a) where
  (==) Test3.Nil Test3.Nil = True
  (==) _ Test3.Nil = False
  (==) Test3.Nil _ = False
  (==) (Test3.Cons a i b) (Test3.Cons c j d) = (a == c) && (b == d)

--uncompress_io x = BackRefs.resolve (toBackRefs (Test3.deflateTestNoBackRefs (bytesToBits (gzStrip x))))

uncompress_io x = Test3.deflateTestNoBackRefs $ bytesToBits $ gzStrip x

mainWithArgs :: [String] -> IO ()
mainWithArgs args = do
  content <- BS.readFile (head args)
  let { !_ = uncompress_io (BS.unpack content) } in print ""

--  print $ uncompress_io $ BS.unpack content
  
  --BS.writeFile (args !! 1) $ convertbytes3 $ uncompress_io (BS.unpack content)

main :: IO ()
main = do
  args <- System.Environment.getArgs
  mainWithArgs args
