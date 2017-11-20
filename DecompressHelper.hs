module DecompressHelper where
import Data.Char
import qualified Data.ByteString as BS
import Data.Word
import Data.Bits
import System.Environment
import Prelude hiding (lookup)
import qualified Extraction
import System.IO
import qualified System.Environment

-- convert vec to list
convertvec :: Extraction.Vec a -> [a]
convertvec (_, l) = l
    
-- convert Coq byte-list to characters
convertbyte :: [Bool] -> Word8
convertbyte l = foldl (\ acc b -> acc * 2 + if b then 1 else 0) 0 (reverse l)

convertbytes2 :: [Extraction.Vec Bool] -> BS.ByteString
convertbytes2 x = BS.pack (map (convertbyte . convertvec) x)

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

bytesToBits :: [Word8] -> [Bool]
bytesToBits [] = []
bytesToBits (x : l) = (intToCode x) ++ (bytesToBits l)
                      
--uncompress_io x = convertbytes2 (EfficientDecompress.efficientDeflate (bytesToBits (gzStrip x)))
     
mainWithArgs :: [String] ->  ([Bool] ->
                              Either [Extraction.Vec Prelude.Bool]
                              [Data.Char.Char]) -> IO ()
mainWithArgs args decompress = do
  content <- BS.readFile (head args)
  let unc = decompress (bytesToBits (gzStrip (BS.unpack content)))
  case unc of
    Left result -> do BS.writeFile (args !! 1) (convertbytes2 result)
    Right error -> do putStrLn error

