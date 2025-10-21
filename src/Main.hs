module Main where

import Common
import Control.Monad (join)
import ExampleCommon
import Gentzen
import Hoare
import Imp
import PrettyPrinter
import TNT
import qualified Data.Map as M

main :: IO ()
main = do
  putStrLn "=== hoareImp Test Runner ==="