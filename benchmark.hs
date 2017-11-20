{-

A simple program that calls the `time` command on a given command,
parses the output, the required time and space, and puts it into a
given SQLite database.

Requires persistent, persistent-template, persistent-sqlite

Invoke with:

./benchmark sqlite-database command args...

License:

Copyright (c) 2017 Christoph-Simon Senjak

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-}

{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

import System.Process
import System.Exit
import System.Environment
import Data.String
import Control.Monad.IO.Class  (liftIO)
import Database.Persist
import Database.Persist.Sqlite
import Database.Persist.TH
import Control.Concurrent
import Control.Monad.Catch
import Database.Sqlite
import Data.Typeable
import qualified Data.Text
    
--import Control.Exception.Base
       
share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
Benchmark
    exitCode String
    stdout String
    stdin String
    stderr String
    maxMemKiBs Int
    kernelSecs Double
    userSecs Double
    runtimeSecs Double -- = kernelSecs + userSecs
    command FilePath
    arguments [String]
    deriving Show
|]

benchmarkProcess :: FilePath
                 -> [String]
                 -> String
                 -> IO Benchmark
benchmarkProcess benchmarkCommand benchmarkArguments benchmarkStdin = do
  (   (show -> benchmarkExitCode)
    , benchmarkStdout
    , benchmarkStderr
    ) <- readProcessWithExitCode
            "/usr/bin/env"
            ([ "time", "-f", "%U %S %M"
               , benchmarkCommand ] ++ benchmarkArguments)
            benchmarkStdin
  let [   (read -> benchmarkUserSecs)
        , (read -> benchmarkKernelSecs)
        , (read -> benchmarkMaxMemKiBs) ] = words benchmarkStderr
  return $ Benchmark { benchmarkRuntimeSecs = benchmarkUserSecs
                                              + benchmarkKernelSecs
                     , .. }

main :: IO ()
main = do
    (dbase : path : args) <- getArgs
    benchResult <- benchmarkProcess path args ""
    doInsertion benchResult dbase
       where
         doInsertion :: Benchmark -> String -> IO ()
         doInsertion d db = do
           catch (do
                   runSqlite (fromString db) $ do
                     runMigration migrateAll
                     key <- insert d
                     return ())
                  (\(e :: SqliteException) ->
                       case seError e of
                         ErrorBusy -> do
                           liftIO $ putStrLn "Database is busy. Retrying."
                           liftIO $ threadDelay 1000
                           liftIO $ doInsertion d db
                         _ -> liftIO $ putStrLn (Data.Text.unpack (seDetails e)))
