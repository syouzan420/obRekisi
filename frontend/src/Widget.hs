module Widget (elButtonMondai, elChara, elSpace) where

import Control.Monad.IO.Class (liftIO,MonadIO)
import Control.Monad.Fix (MonadFix)
import qualified Data.Text as T

import Obelisk.Generated.Static (static)

import EReki (Rdt(..), reki, sortNens)

import Reflex.Dom.Core 
  ( text, dynText, el, elAttr, divClass, elAttr', blank
  , (=:), leftmost, accumDyn, elDynAttr, prerender
  , holdDyn, domEvent, zipDynWith
  , tickLossyFromPostBuildTime, widgetHold_
  , DomBuilder, Prerender, PerformEvent, TriggerEvent
  , PostBuild, Event, EventName(Click), MonadHold ,Dynamic
  , Performable, TickInfo(..)
  )

data Button = ButtonNumber T.Text | ButtonClear 

elSpace :: DomBuilder t m => m ()
elSpace = el "p" $ text ""

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
  tb <- (elButtonAction <$) <$> buttonClass "pad2" "もんだい" 
  el "p" $ text ""
  widgetHold_ elButtonAction tb 


buttonClass :: DomBuilder t m => T.Text -> T.Text -> m (Event t ())
buttonClass c s = do
  (e, _) <- elAttr' "button" ("type" =: "button" <> "class" =: c) $ text s
  return $ domEvent Click e

numberPad :: DomBuilder t m => Int -> m (Event t T.Text)
numberPad i = do
  b1 <- ("1" <$) <$> numberButton "1"
  b2 <- ("2" <$) <$> numberButton "2"
  b3 <- ("3" <$) <$> numberButton "3"
  b4 <- ("4" <$) <$> numberButton "4"
  b5 <- ("5" <$) <$> numberButton "5"
  return $ leftmost (take i [b1,b2,b3,b4,b5])
  where
    numberButton = buttonClass "pad" 

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
  elCharaAnime
  el "p" $ text ""
  (dyAns,dyRdt) <- elMondai
  let dyMon = fmap makeMon dyRdt
  divClass "kai" (dynText dyMon)
  el "p" $ text ""
  numberButton <- numberPad 5
  clearButton <- buttonClass "pad" "C"
  let buttons = leftmost [ ButtonClear <$ clearButton
                         , ButtonNumber <$> numberButton
                         ]
  dyState <- accumDyn collectButtonPresses initialState buttons
  let dyKoto = fmap makeKoto dyRdt
  let dyRes = zipDynWith (\a b->if a==b then "せいかい!" else T.empty) dyAns dyState 
      dyRes2 = zipDynWith (\a b-> if a/=T.empty then b else T.empty) dyRes dyKoto
  el "p" $ dynText dyState
  el "p" $ dynText dyRes
  divClass "kai" $ dynText dyRes2
  where
    initialState :: T.Text
    initialState = T.empty

    collectButtonPresses :: T.Text -> Button -> T.Text
    collectButtonPresses state buttonPress =
      case buttonPress of
        ButtonClear -> initialState
        ButtonNumber digit -> state <> digit

elMondai :: 
  ( DomBuilder t m
  , Prerender t m
  ) => m (Dynamic t T.Text, Dynamic t [Rdt]) 
elMondai = do
  dyRdtAns <- prerender (return ([],[])) $ liftIO $ reki 5
  let dyRdt = fmap fst dyRdtAns
      dyAns = fmap makeAns dyRdtAns
  return (dyAns,dyRdt) 

makeAns :: ([Rdt],[Int]) -> T.Text
makeAns (_,ils) = (T.pack . concatMap show) ils

makeMon :: [Rdt] -> T.Text
makeMon rdt = T.intercalate "\n" $
       zipWith (\i (Rdt _ k _ _) -> (T.pack . show) i <> ": " <> k) [1::Int,2..] rdt

makeKoto :: [Rdt] -> T.Text
makeKoto rdt = T.intercalate "\n" $
              map (\(n,k) -> (T.pack . show) n <> "年: " <> k) $
              sortNens $ map (\(Rdt n k _ _) -> (n,k)) rdt 

elTimer :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , TriggerEvent t m
  ) => m (Dynamic t T.Text)
elTimer = do
  evTime <- tickLossyFromPostBuildTime 1 
  let evTimeText = T.pack . show . (+1) . _tickInfo_n <$> evTime
  holdDyn "start" evTimeText 
  
elCharaAnime :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , TriggerEvent t m
  ) => m ()
elCharaAnime = do
  dyTime <- elTimer
  let dToggle = fmap (\tx -> (tx/="start") &&
                     (rem ((read . T.unpack) tx) 2==(0::Int))) dyTime
  let 
    dNotToggle = not <$> dToggle
    mkHidden False = "hidden" =: ""
    mkHidden True = mempty
    dHide1 = mkHidden <$> dToggle
    dHide2 = mkHidden <$> dNotToggle
  el "p" $ text ""
  elDynAttr "div" dHide1 $ do elChara0; dynText dyTime 
  elDynAttr "div" dHide2 $ do elChara1; dynText dyTime 
  pure ()
  
elChara :: DomBuilder t m => m ()
elChara = elAttr "img" ("src" =: $(static "chara0_mid.png")) blank

elChara0 :: DomBuilder t m => m ()
elChara0 = elAttr "img" ("src" =: $(static "chara0.png")) blank

elChara1 :: DomBuilder t m => m ()
elChara1 = elAttr "img" ("src" =: $(static "chara1.png")) blank

