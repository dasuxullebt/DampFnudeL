module Main where
import Data.Char
import qualified Data.ByteString as BS
import Data.Word
import Data.Bits
import System.Environment
import Prelude hiding (lookup)

import qualified DiffStack
import qualified Extraction
import DecompressHelper

import System.IO
import qualified System.Environment
     
main :: IO ()
main = do
  args <- System.Environment.getArgs
  mainWithArgs args DiffStack.efficientDeflate
