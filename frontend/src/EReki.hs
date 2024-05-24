{-# LANGUAGE OverloadedStrings #-}
module EReki (Rdt(..), reki, sortNens) where

import System.Random (randomRIO)
import qualified Data.Text as T

--import File (fileRead)
import Reki (rekiDoc, rekiDoc2)

type Nen = Int
type Koto = T.Text
type Hint = T.Text
type Content = T.Text
data Rdt = Rdt Nen Koto Hint Content

sortNens :: [(Int,a)] -> [(Int,a)]
sortNens [] = []
sortNens ((x,a):xs) = 
    sortNens (smaller xs) <> [(x,a)] <> sortNens (larger xs)
  where smaller ls = [(p,q)|(p,q)<-ls,p<x]
        larger ls = [(p,q)|(p,q)<-ls,p>=x]

makeJun :: [Rdt] -> [Int]
makeJun rdt = let nens = map (\(Rdt n _ _ _) -> n) rdt
               in map snd (sortNens (zip nens [1,2..]))  

getRan :: Int -> IO Int
getRan i = randomRIO (0,i)

delFromList :: Int -> [a] -> [a]
delFromList i ls = if length ls < i+1 then ls else take i ls <> drop (i+1) ls 

selectData :: Int -> [a] -> IO [a] 
selectData 0 _ = return [] 
selectData i rdt = do 
  rn <- getRan (length rdt - 1)
  let dt = rdt!!rn
      dts = delFromList rn rdt
  sdts <- selectData (i-1) dts
  return (dt:sdts)

reki :: Int -> Int -> IO ([Rdt],[Int]) 
reki t i = do
  let txs = T.lines (if t==2 then rekiDoc2 else rekiDoc) 
  let rdts = map makeRData txs
  mondai <- selectData i rdts 
  let jun = makeJun mondai
  return (mondai,jun)

makeRData :: T.Text -> Rdt
makeRData tx =
  let sps = T.splitOn "," tx
      nen = (read . T.unpack . head) sps 
   in case length sps of
        0 -> Rdt 0 T.empty T.empty T.empty
        1 -> Rdt nen T.empty T.empty T.empty
        2 -> Rdt nen (sps!!1) "noHint" "noContent" 
        3 -> Rdt nen (sps!!1) (sps!!2) "noContent"
        _ -> Rdt nen (sps!!1) (sps!!2) (sps!!3)

