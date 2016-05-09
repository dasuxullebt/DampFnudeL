module Main where
import Data.Char
import qualified Data.ByteString as BS
import Data.Word
import Data.Bits
import System.Environment
import qualified Test
import Prelude hiding (lookup)

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

-- Convert the result of Test.deflateTest to something readable
deflateResult (Left y) = "Success: " ++ (convertbytes y)
deflateResult (Right y) = "Failure: " ++ y 

-- uncompress a string of 0 and 1's that may contain other characters which are to be ignored
uncompress :: String -> String
uncompress =  deflateResult . Test.deflateTest . toboollist

-- banana_ananas_batata example from paper
banana_ananas_batata = uncompress "\
\1 0 1\
\11000 10100 0111\
\\
\000 110 110 110 000 000 000 000 000\
\000 000 010 000 010 000 001 000 001\
\\
\110 0010101 01 100 00 00 110 0000000 00 101 100 01 00\
\110 1111111 100 01 1111 100 01 100 1110 101 000 1110\
\\
\010 100 00 0 1101 1100 011 1111 1 1 00 1 0 101 00 0 1110\
\\
\0000000"

-- shorter banana_ananas_batata example from paper
banana_ananas_batata_short = uncompress "\
\1 1 0\
\\
\10010001 10011110 0000001 00001 10100011 10001111 10010010\
\0000011 00101 1 0000001 00101 0 10100100 0000001 00001\
\0000000\
\\
\0000"

-- to apply it to gz-files

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

uncompress_io_result (Left x) = Left (convertbytes2 x)
uncompress_io_result (Right x) = Right x

uncompress_io x = uncompress_io_result (Test.deflateTest (bytesToBits (gzStrip x)))
     
mainWithArgs :: [String] -> IO ()
mainWithArgs args = do
  content <- BS.readFile (head args)
  case uncompress_io (BS.unpack content) of
    Right x -> print $ "Error: " ++ x
    Left x -> do
      print "Success."
      BS.writeFile (args !! 1) x

main :: IO ()
main = do
  args <- System.Environment.getArgs
  mainWithArgs args
