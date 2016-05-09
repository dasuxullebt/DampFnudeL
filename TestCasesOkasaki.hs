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
import qualified Okasaki

-- remove everything except 0 and 1
rmcomments :: String -> String
rmcomments [] = []
rmcomments ('1' : r) = '1' : rmcomments r
rmcomments ('0' : r) = '0' : rmcomments r
rmcomments (_ : r) = rmcomments r

bitAccum acc b = acc * 2 + if b then 1 else 0
listToByte l = foldl bitAccum 0 l

-- convert Coq byte-list to characters
convertbyte :: Okasaki.CatDeque Bool -> Word8
convertbyte l = listToByte (Okasaki.cdToListR l)

convertbytes2 :: Okasaki.CatDeque (Okasaki.CatDeque Bool) -> BS.ByteString
convertbytes2 x = BS.pack (map convertbyte (Okasaki.cdToListL x))

-- Convert the result of Test.deflateTest to something readable
deflateResult (Left y) = "Success"
deflateResult (Right y) = "Failure: " ++ y 

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
intToCode :: Word8 -> Okasaki.CatDeque Bool
intToCode c = Okasaki.cdOfListL $ map (testBit c) [0..7]

reverseBits :: Word8 -> Word8
reverseBits a = listToByte $ map (testBit a) [ 7 - x | x <- [0..7]]

w8t64 :: [Word8] -> Word64
w8t64 b =
    foldl (.|.) 0 $ map (\ (x, y) -> shiftL ((fromIntegral x) :: Word64) (8 * y)) $ zip b [0..]
            
bytesToBitsL :: [Word8] -> Okasaki.List Bool
bytesToBitsL [] = Okasaki.Nil
bytesToBitsL x = let (beg, end) = splitAt 8 x
                 in case end of
                      [] -> Okasaki.BCons (fromIntegral $ 8 * (length beg) - 1) (w8t64 beg) Okasaki.Nil
                      _ -> Okasaki.BCons 63 (w8t64 beg) $ bytesToBitsL end

bytesToBits :: [Word8] -> Okasaki.CatDeque Bool
bytesToBits m = let len = length m
                    (l, r_) = splitAt (len `div` 2) m
                    r = reverse $ map reverseBits r_
                in Okasaki.CDNode $ Okasaki.Queue { Okasaki.qLength = len,
                                                    Okasaki.leftList = bytesToBitsL l,
                                                    Okasaki.rightList = bytesToBitsL r }
uncompress_io_result (Left x) = Left (convertbytes2 x)
uncompress_io_result (Right x) = Right x

uncompress_io x = uncompress_io_result (Test.deflateTest (bytesToBits (gzStrip x)))
{-  
mainWithArgs :: [String] -> IO ()
mainWithArgs args = do
  content <- BS.readFile (head args)
  case uncompress_io (BS.unpack content) of
    Right x -> print $ "Error: " ++ x
    Left x -> do
      print "Success."
      BS.writeFile (args !! 1) x
--}

mainWithArgs :: [String] -> IO ()
mainWithArgs args = do
  content <- BS.readFile (head args)
  print $ show $ Okasaki.qPopLeft $ Okasaki.qPushRightList (replicate 99 True) Okasaki.qEmpty --(bytesToBits $ BS.unpack content)

        
main :: IO ()
main = do
  args <- System.Environment.getArgs
  mainWithArgs args
