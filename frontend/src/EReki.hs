{-# LANGUAGE OverloadedStrings #-}
module EReki (reki, sortNens) where

import System.Random (randomRIO)
import qualified Data.Text as T

type ERData = (Int,String)

erekiData :: [ERData]
erekiData = [(57,"奴国王が後漢から金印")
            ,(239,"「卑弥呼」が魏に遣使")
            ,(316,"仁徳天皇 税を免除")
            ,(479,"「倭」の武王 南朝の宋へ遣使")
            ,(538,"仏教公伝")
            ,(604,"十七条憲法制定")
            ,(645,"乙巳の変")
            ,(672,"壬申の乱")
            ,(710,"平城京遷都")
            ,(794,"平安京遷都")
            ,(806,"最澄が天台宗 空海が真言宗")
            ,(857,"藤原良房が太政大臣に")
            ,(935,"承平天慶の乱")
            ,(1016,"藤原道長が摂政に")
            ,(1086,"院政開始")
            ,(1167,"平清盛が太政大臣に")
            ,(1185,"平家滅亡")
            ,(1192,"源頼朝が征夷大将軍に")
            ,(1221,"承久の乱")
            ,(1334,"建武の新政")
            ,(1338,"室町幕府成立")
            ,(1429,"琉球統一")
            ,(1467,"応仁の乱")
            ,(1495,"北条早雲が小田原入城")
            ,(1542,"斎藤道三が美濃を奪う")
            ,(1553,"川中島の戦い")
            ,(1560,"桶狭間の戦い")
            ,(1592,"文禄の役")
            ,(1590,"豊臣秀吉の天下統一")
            ,(1600,"関ヶ原の戦い")
            ,(1637,"島原の乱")
            ,(1685,"生類憐みの令")
            ,(1716,"享保の改革")
            ,(1767,"田沼意次の政治")
            ,(1837,"大塩平八郎の乱")
            ,(1854,"日米和親条約")
            ,(1860,"桜田門外の変")
            ,(1868,"明治維新")
            ,(1871,"日清修好条規")
            ,(1875,"江華島事件")
            ,(1877,"西南戦争")
            ,(1885,"天津条約")
            ,(1894,"日清戦争")
            ,(1899,"義和団事変")
            ,(1900,"ロシア満洲占領")
            ,(1902,"日英同盟")
            ,(1904,"日露戦争")
            ,(1931,"満洲事変")
            ,(1937,"支那事変")
            ,(1941,"大東亜戦争")
            ,(1945,"ポツダム宣言")
            ,(1951,"サンフランシスコ平和条約")
            ]

sortNens :: [(Int,a)] -> [(Int,a)]
sortNens [] = []
sortNens ((x,a):xs) = 
    sortNens (smaller xs) <> [(x,a)] <> sortNens (larger xs)
  where smaller ls = [(p,q)|(p,q)<-ls,p<x]
        larger ls = [(p,q)|(p,q)<-ls,p>=x]

makeJun :: [ERData] -> [Int]
makeJun erd = let nens = map fst erd
               in map snd (sortNens (zip nens [1,2..]))  

--showERData :: ERData -> String
--showERData (nen,koto) = show nen <> "年: " <> koto

getRan :: Int -> IO Int
getRan i = randomRIO (0,i)

delFromList :: Int -> [a] -> [a]
delFromList i ls = if length ls < i+1 then ls else take i ls <> drop (i+1) ls 

selectData :: Int -> [ERData] -> IO [ERData] 
selectData 0 _ = return [] 
selectData i erd = do 
  rn <- getRan (length erd - 1)
  let dt = erd!!rn
      dts = delFromList rn erd
  sdts <- selectData (i-1) dts
  return (dt:sdts)

{-
main :: IO ()
main = do
  mondai <- selectData 3 erekiData
  let jun = makeJun mondai
  let juns = concatMap show jun 
  mapM_ (putStrLn . (\(i,s) -> show i <> " :" <> s)) $ zip [0,1..] (map snd mondai)
  putStrLn "古い順にならべてください"
  gl <- getLine
  let res = if gl==juns then "せいかい！！！" else "ちがいます！！！"
  putStrLn res
  mapM_ (putStrLn . showERData . (!!) mondai) jun  
-}

reki :: Int -> IO T.Text
reki i = do
  mondai <- selectData i erekiData
  let jun = makeJun mondai
  let juns = concatMap show jun
  let montx = T.intercalate "," $ map makeMonTex mondai
  return (montx <> "=" <> T.pack juns)

makeMonTex :: ERData -> T.Text
makeMonTex (nen,koto) = T.pack (show nen <> "-" <> koto)
