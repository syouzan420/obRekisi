module Widget (elButtonMondai, elChara, elSpace) where

import Control.Monad.IO.Class (liftIO,MonadIO)
import Control.Monad.Fix (MonadFix)
import qualified Data.Text as T
import Data.Map.Strict (Map)

import Obelisk.Generated.Static (static)

import EReki (Rdt(..), reki, sortNens)

import Reflex.Dom.Core 
  ( text, dynText, el, elAttr, divClass, elAttr', blank
  , (=:), leftmost, accumDyn, elDynAttr, elDynAttr', prerender 
  , holdDyn, domEvent, zipDynWith, current, gate, toggle
  , tickLossyFromPostBuildTime, widgetHold_
  , tag
  , DomBuilder, Prerender, PerformEvent, TriggerEvent
  , PostBuild, Event, EventName(Click), MonadHold ,Dynamic
  , Performable, TickInfo(..)
  )

data Button = ButtonNumber T.Text | ButtonBack 

qNum :: Int
qNum = 5

mkHidden :: Bool -> Map T.Text T.Text
mkHidden False = "hidden" =: "" 
mkHidden True = mempty

getItem :: Int -> [a] -> Maybe a
getItem _ [] = Nothing
getItem i ls = if length ls > i then Just (ls!!i) else Nothing

getRdt :: Int -> [Rdt] -> Rdt
getRdt i rdts = case getItem i rdts of
                  Just rdt -> rdt
                  Nothing -> Rdt 0 T.empty T.empty T.empty

makeAns :: ([Rdt],[Int]) -> T.Text
makeAns (_,ils) = (T.pack . concatMap show) ils

makeSort :: [Rdt] -> [Rdt]
makeSort rdt = map (\(n,(k,h,c)) -> Rdt n k h c) $
                  sortNens $ map (\(Rdt n k h c) -> (n,(k,h,c))) rdt 

elSpace :: DomBuilder t m => m ()
elSpace = el "p" $ text ""

elChara :: DomBuilder t m => m ()
elChara = elAttr "img" ("src" =: $(static "chara0_mid.png")) blank

elButtonMondai :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , Prerender t m
  , TriggerEvent t m
  ) => m ()
elButtonMondai = do
  tb <- (elButtonAction <$) <$> evElButton "pad2" "もんだい" 
  el "p" $ text ""
  widgetHold_ elButtonAction tb 

elButtonAction :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , Prerender t m
  , TriggerEvent t m
  ) => m ()
elButtonAction = do
  rec
    (dyAns,dyRdt) <- elMondai
    dyTime <- elCharaAnime (fmap not dyIsAnsCorrect)
    let dyIsTime60 = 
          fmap (\ti -> (ti/="start") && (read . T.unpack) ti>(60::Int)) dyTime
    elSpace
    mapM_ (\n -> elOneMon dyIsTime60 (n+1) (fmap (getRdt n) dyRdt)) [0..(qNum-1)]
    elSpace
    evNumberButtons <- evElNumberPad qNum 
    evBackButton <- evElButton "pad" "B"
    let evButtons = leftmost [ ButtonBack <$ evBackButton
                           , ButtonNumber <$> evNumberButtons
                           ]
    dyState <- accumDyn collectButtonPresses initialState evButtons
    let dyIsAnsCorrect = zipDynWith (==) dyAns dyState
    el "p" $ dynText dyState
    elKai dyIsAnsCorrect dyRdt
  pure ()
  where
    initialState :: T.Text
    initialState = T.empty

    collectButtonPresses :: T.Text -> Button -> T.Text
    collectButtonPresses state buttonPress =
      case buttonPress of
        ButtonBack -> if state==T.empty then T.empty else T.init state 
        ButtonNumber digit -> state <> digit

evElButton :: DomBuilder t m => T.Text -> T.Text -> m (Event t ())
evElButton c s = do
  (e, _) <- elAttr' "button" ("type" =: "button" <> "class" =: c) $ text s
  return $ domEvent Click e

evElButtonH :: 
  ( DomBuilder t m
  , PostBuild t m
  ) => Dynamic t Bool -> T.Text -> T.Text -> m (Event t ())
evElButtonH dyB c s = do
  (e, _) <- elDynAttr' "button" dyBHide $ text s 
  return $ domEvent Click e
  where mkHidden' False = "hidden" =: "" <> otherAttr 
        mkHidden' True = otherAttr 
        dyBHide = mkHidden' <$> dyB
        otherAttr = "type" =: "button" <> "class" =: c

evElNumberPad :: DomBuilder t m => Int -> m (Event t T.Text)
evElNumberPad i = do
  evts <- mapM (\n -> (toText n <$) <$> evElNumberButton (toText n)) [1..i] 
  return $ leftmost evts
  where
    evElNumberButton = evElButton "pad" 
    toText = T.pack . show

elOneMon :: 
  ( DomBuilder t m
  , MonadHold t m
  , MonadFix m
  , PostBuild t m
  )  => Dynamic t Bool -> Int -> Dynamic t Rdt -> m ()
elOneMon dyIsTime60 i dyRdt = do
  divClass "kai" $ do 
    let dHide = mkHidden <$> dyIsTime60
    let dyMon = fmap (\(Rdt _ k _ _) -> 
                      (T.pack . show) i <> ": " <> k) dyRdt 
    dynText dyMon
    elDynAttr "div" dHide $ do 
      rec
        let dyH = fmap (\(Rdt _ _ h _) -> "-----"<>h) dyRdt
        let beH = current dyH
        evB <- evElButtonH dyToggle "text" "hint"
        dyToggle <- toggle True evB
        let evH = tag beH evB
        dynText =<< holdDyn T.empty evH 
        blank
      pure ()

elKai ::
  ( DomBuilder t m
  , MonadHold t m
  , MonadFix m
  , PostBuild t m
  ) => Dynamic t Bool -> Dynamic t [Rdt] -> m ()
elKai dyIsAnsCorrect dyRdt = do
  let dHide = mkHidden <$> dyIsAnsCorrect
  let dySRdt = fmap makeSort dyRdt
  elDynAttr "div" dHide $ do 
    el "p" $ text "せいかい!"
    elSpace
    mapM_ (\n -> elOneKai (fmap (getRdt n) dySRdt)) [0..(qNum-1)]

elOneKai :: 
  ( DomBuilder t m
  , MonadHold t m
  , MonadFix m
  , PostBuild t m
  )  => Dynamic t Rdt -> m ()
elOneKai dyRdt = do
  divClass "kai" $ do 
    rec
      dynText $ fmap (\(Rdt n k _ _) -> (T.pack . show) n <> "年: " <> k) dyRdt
      text "  "
      let dyC = fmap (\(Rdt _ _ _ c) -> "\n-----"<>c<>"\n ") dyRdt
      let beC = current dyC
      evB <- evElButtonH dyToggle "text" "more"
      dyToggle <- toggle True evB
      let evC = tag beC evB
      dynText =<< holdDyn T.empty evC 
      blank
    pure ()

elMondai :: 
  ( DomBuilder t m
  , Prerender t m
  ) => m (Dynamic t T.Text, Dynamic t [Rdt]) 
elMondai = do
  dyRdtAns <- prerender (return ([],[])) $ liftIO $ reki qNum 
  let dyRdt = fmap fst dyRdtAns
      dyAns = fmap makeAns dyRdtAns
  return (dyAns,dyRdt) 

elTimer :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , TriggerEvent t m
  ) => Dynamic t Bool -> m (Dynamic t T.Text)
elTimer isAnsNotCorrect = do
  evTime <- tickLossyFromPostBuildTime 1 
  let beBool = current isAnsNotCorrect 
  let evNTime = gate beBool evTime
  let evTimeText = T.pack . show . (+1) . _tickInfo_n <$> evNTime
  holdDyn "start" evTimeText 
  
elCharaAnime :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , TriggerEvent t m
  ) => Dynamic t Bool -> m (Dynamic t T.Text)
elCharaAnime isAnsNotCorrect = do
  dyTime <- elTimer isAnsNotCorrect 
  let dToggle = fmap (\tx -> (tx/="start") &&
                     (rem ((read . T.unpack) tx) 2==(0::Int))) dyTime
  let 
    dNotToggle = not <$> dToggle
    dHide1 = mkHidden <$> dToggle
    dHide2 = mkHidden <$> dNotToggle
  el "p" $ text ""
  elDynAttr "div" dHide1 $ do elChara0; dynText dyTime 
  elDynAttr "div" dHide2 $ do elChara1; dynText dyTime 
  pure dyTime 
  
elChara0 :: DomBuilder t m => m ()
elChara0 = elAttr "img" ("src" =: $(static "chara0.png")) blank

elChara1 :: DomBuilder t m => m ()
elChara1 = elAttr "img" ("src" =: $(static "chara1.png")) blank

