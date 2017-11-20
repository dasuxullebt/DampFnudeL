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
     
mainWithArgs :: [String] -> IO ()
mainWithArgs args = do
  content <- BS.readFile (head args)
  let unc = NoRBR.deflateNoRBR
            (bytesToBits (gzStrip (BS.unpack content)))
  putStrLn $ show unc
            
main :: IO ()
main = do
  args <- System.Environment.getArgs
  mainWithArgs args
