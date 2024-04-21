{-# LANGUAGE OverloadedStrings #-}
module Convert where

import qualified Data.Text as T

import File (fileRead, fileWrite)

conv :: IO ()
conv = do
  lns <- T.lines <$> fileRead inputFile 
  let res = "module Reki (rekiDoc) where\n\nimport qualified Data.Text as T\n\nrekiDoc :: T.Text\nrekiDoc = \"" <> T.intercalate "\\n" lns <> "\""
  fileWrite outputFile res

inputFile :: FilePath
inputFile = "../../assets/reki.txt"

outputFile :: FilePath
outputFile = "Reki.hs"
