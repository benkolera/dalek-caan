module Main where

import System.IO (IO)
import Test.DocTest

main :: IO ()
main = doctest [
  "-packageghc"
  , "-isrc"
  , "-idist/build/autogen/"
  , "-optP-include"
  , "-optPdist/build/autogen/cabal_macros.h"
  , "-XOverloadedStrings"
  , "src/Bot.hs"
  ]
