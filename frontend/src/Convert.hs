{-# LANGUAGE OverloadedStrings #-}
module Convert where

import qualified Data.Text as T

import File (fileRead, fileWrite)

conv :: IO ()
conv = do
  lns <- T.lines <$> fileRead inputFile 
  lns2 <- T.lines <$> fileRead inputFile2
  let res = "module Reki (rekiDoc, rekiDoc2) where\n\nimport qualified Data.Text as T\n\nrekiDoc :: T.Text\nrekiDoc = \"" <> T.intercalate "\\n" lns <> "\"\n\nrekiDoc2 :: T.Text\nrekiDoc2 = \"" <> T.intercalate "\\n" lns2 <> "\""
  fileWrite outputFile res

inputFile :: FilePath
inputFile = "../../assets/reki.txt"

inputFile2 :: FilePath
inputFile2 = "../../assets/reki2.txt"

outputFile :: FilePath
outputFile = "Reki.hs"
