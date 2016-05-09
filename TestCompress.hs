{-# LANGUAGE BangPatterns #-}
module Main where
import Data.Char
import qualified Data.ByteString as BS
import Data.Word
import Data.Bits
import Data.Digest.CRC32
import System.Environment
import qualified CompressX
import Prelude hiding (lookup)

import System.IO
--import Data.Map ((!), Map)
import qualified System.Environment

-- convert Coq byte-list to characters
convertbyte :: [Bool] -> Word8
convertbyte l = foldl (\ acc b -> acc * 2 + if b then 1 else 0) 0 (reverse l)
--convertbyte l = foldl (\ acc b -> (shift acc 1) .|. (if b then bit 0 else 0)) 0 (reverse l)

convertToBytes :: [Bool] -> [Word8]
convertToBytes [] = []
convertToBytes c = let (a, r) = splitAt 8 c
                   in (convertbyte a) : convertToBytes r

convertToByteString = BS.pack . convertToBytes

lToT :: [a] -> CompressX.T a
lToT l = let k = length l
             lt _ [] = CompressX.Nil
             lt n (x : a) = CompressX.Cons x n $ lt (n - 1) a
         in lt k l

-- convert bytes to boolean list
intToCode :: Word8 -> [Bool]
intToCode c = map (testBit c) [0..7]

bytesToCoq :: [Word8] -> [CompressX.T Bool]
bytesToCoq = map (lToT . intToCode)

-- create a gzip file from compressed and cleartext data

lsbW32 :: Word32 -> [Word8]
lsbW32 w32 = map (\x-> fromIntegral $ (w32 `shiftR` (x * 8)) .&. 0xFF) [0, 1, 2, 3]

gzClad :: [Word8] -> [Word8] -> [Word8]
gzClad compressed uncompressed =
       let { c32 = crc32 uncompressed
           ; l = length uncompressed }
       in [ 0x1f, 0x8b, -- ID1, ID2
            0x08, -- CM = deflate
            0x00, -- FLG = no extra/name/comment/text
            0x00, 0x00, 0x00, 0x00, -- MTIME not available
            0x02, -- we use a sophisticated algorithm
            0xff ] -- and our OS is probably unknown
            ++ compressed
            ++ (lsbW32 c32) ++ (lsbW32 (fromIntegral l))

uncompress_io x = gzClad (convertToBytes (CompressX.compressX (bytesToCoq x))) x

mainWithArgs :: [String] -> IO ()
mainWithArgs args = do
  content <- BS.readFile (head args)
  BS.writeFile (args !! 1) $ BS.pack $ uncompress_io (BS.unpack content)

main :: IO ()
main = do
  args <- System.Environment.getArgs
  mainWithArgs args
