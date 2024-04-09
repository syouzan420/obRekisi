{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeFamilies #-}

module Frontend where

import Common.Api (commonStuff)
import Common.Route (FrontendRoute (..))
--import Control.Lens ((^.))
--import Control.Monad
import Control.Monad.IO.Class (liftIO,MonadIO)
import Control.Monad.Fix (MonadFix)
import qualified Data.Text as T
--import qualified Data.Text.Encoding as T
--import Language.Javascript.JSaddle (liftJSM, js, js1, jsg)

--import Data.Time.Clock (getCurrentTime,UTCTime)

import Obelisk.Frontend
--import Obelisk.Configs
import Obelisk.Route
-- import Obelisk.Route.Frontend
import Obelisk.Generated.Static (static)

import qualified Page.About as About

import EReki (ERData, reki, sortNens)

import Reflex.Dom.Core 
  ( text, dynText, el, elAttr, divClass, elAttr', blank
  , (=:), leftmost, accumDyn, elDynAttr, prerender
  , widgetHold_, holdDyn, domEvent, toggle, zipDynWith
  , tickLossyFromPostBuildTime, never
  , DomBuilder, Prerender, PerformEvent, TriggerEvent
  , PostBuild, Event, EventName(Click), MonadHold ,Dynamic
  , Performable, TickInfo(..)
  )

data Button = ButtonNumber T.Text | ButtonClear 


frontend :: Frontend (R FrontendRoute)
frontend = Frontend
  { _frontend_head = frontendHead 
  , _frontend_body = frontendBody 
  }

frontendHead :: DomBuilder t m => m ()
frontendHead = do
  el "title" $ text "Rekisi"
  elAttr
    "meta"
    ( "name" =: "viewport"
        <> "contents" =: "width=device-width, initial-scale=1.0"
    )
    blank

  elAttr
    "link"
    ("href" =: $(static "main.css")
      <> "type" =: "text/css"
      <> "rel" =: "stylesheet")
    blank

frontendBody :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , Prerender t m
  , TriggerEvent t m
  ) => m ()
frontendBody = do
  el "h1" $ text "國史 ならびかへ"

  el "p" $ text $ T.pack commonStuff

  el "p" $ text ""

  el "div" elChara

  el "p" $ text ""

--  el "div" $ routeLink (FrontendRoute_Main :/ () ) $ button "もんだい" 

  el "div" $ do
    tb <- (elButtonAction <$) <$> buttonClass "pad2" "もんだい" 
    el "p" $ text ""
    widgetHold_ elButtonAction tb 

  el "p" $ text ""
  
  return ()

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
  el "div" elCharaAnime
  el "p" $ text ""
  (dyAns,dyKoto) <- elMondai
  el "p" $ text ""
  numberButton <- numberPad 5
  clearButton <- buttonClass "pad" "C"
  let buttons = leftmost [ ButtonClear <$ clearButton
                         , ButtonNumber <$> numberButton
                         ]
  dyState <- accumDyn collectButtonPresses initialState buttons
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
  , PostBuild t m
  ) => m (Dynamic t T.Text, Dynamic t T.Text) 
elMondai = do
  dyMonText <- prerender (return ([],[])) $ liftIO $ reki 5
  let dyMon = fmap makeMon dyMonText
      dyAns = fmap makeAns dyMonText
      dyKoto = fmap makeKoto dyMonText
  divClass "kai" (dynText dyMon)
  return (dyAns,dyKoto) 

makeAns :: ([ERData],[Int]) -> T.Text
makeAns (_,ils) = (T.pack . concatMap show) ils

makeMon :: ([ERData],[Int]) -> T.Text
makeMon (edt,_) = T.intercalate "\n" $
       zipWith (\i (_,d) -> (T.pack . show) i <> ": " <> d) [1::Int,2..] edt

makeKoto :: ([ERData],[Int]) -> T.Text
makeKoto (erd,_) = T.intercalate "\n" $
              map (\(n,d) -> (T.pack . show) n <> "年: " <> d) $
              sortNens erd 

elTimer :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , TriggerEvent t m
  ) => m ()
elTimer = do
  tev <- tickLossyFromPostBuildTime 1 
  let tm = T.pack . show . (+1) . _tickInfo_n <$> tev
  dynText =<< holdDyn "start" tm 
  pure ()
  
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
  evTick <- tickLossyFromPostBuildTime 1 
  dToggle <- toggle True evTick
  let 
    dNotToggle = not <$> dToggle
    mkHidden False = "hidden" =: ""
    mkHidden True = mempty
    dHide1 = mkHidden <$> dToggle
    dHide2 = mkHidden <$> dNotToggle
  el "p" $ text ""
  elDynAttr "div" dHide1 $ do elChara0; elTimer
  elDynAttr "div" dHide2 $ do elChara1; elTimer
  pure ()
  
elChara :: DomBuilder t m => m ()
elChara = elAttr "img" ("src" =: $(static "chara0_mid.png")) blank

elChara0 :: DomBuilder t m => m ()
elChara0 = elAttr "img" ("src" =: $(static "chara0.png")) blank

elChara1 :: DomBuilder t m => m ()
elChara1 = elAttr "img" ("src" =: $(static "chara1.png")) blank

elCharaShow :: DomBuilder t m => Integer -> m ()
elCharaShow i = do
  let remain = rem i 2 
  case remain of 0 -> elChara0; 1 -> elChara1; _ -> elChara0

route ::
  ( DomBuilder t m
  ) => R FrontendRoute -> m (Event t ())
route (MkHome :/ ()) = pure never
route (MkAbout :/ ()) = About.page >> pure never
