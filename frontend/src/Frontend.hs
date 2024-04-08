{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}

module Frontend where

import Common.Api (commonStuff)
import Common.Route
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

import EReki (reki,sortNens)

import Reflex.Dom.Core 
  ( text, dynText, el, elAttr, divClass, elAttr', blank
  , (=:), leftmost, button, accumDyn, elDynAttr, prerender
  , widgetHold_, holdDyn, domEvent, toggle, zipDynWith
  , tickLossyFromPostBuildTime
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

  el "div" chara

  el "p" $ text ""

--  el "div" $ routeLink (FrontendRoute_Main :/ () ) $ button "もんだい" 

  el "div" $ do
    tb <- (buttonAction <$) <$> buttonClass "pad2" "もんだい" 
    el "p" $ text ""
    widgetHold_ buttonAction tb 
    blank

  el "p" $ text ""
  
  return ()

monButton :: DomBuilder t m => m (Event t ())   
monButton = el "div" (button "もんだい")

buttonClass :: DomBuilder t m => T.Text -> T.Text -> m (Event t ())
buttonClass c s = do
  (e, _) <- elAttr' "button" ("type" =: "button" <> "class" =: c) $ text s
  return $ domEvent Click e

reloadButton :: DomBuilder t m => m (Event t ())  
reloadButton = do
  (e, _) <- elAttr' "button" ("type" =: "button" <> "class" =: "pad" <> "onClick" =: "location.reload(true);") $ text "OK"
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

buttonAction :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , Prerender t m
  , TriggerEvent t m
  ) => m ()
buttonAction = do
  el "div" charaAnime
  el "p" $ text ""
  (ans,koto) <- mondai
  el "p" $ text ""
  numberButton <- numberPad 5
  clearButton <- buttonClass "pad" "C"
  let buttons = leftmost [ ButtonClear <$ clearButton
                         , ButtonNumber <$> numberButton
                         ]
  dstate <- accumDyn collectButtonPresses initialState buttons
  let res = zipDynWith (\a b->if a==b then "せいかい!" else T.empty) ans dstate 
      res2 = zipDynWith (\a b-> if a/=T.empty then b else T.empty) res koto
  el "p" $ do
    dynText dstate
    blank
  el "p" $ do
    dynText res 
    blank
  divClass "kai" $ do
    dynText res2 
    blank
  where
    initialState :: T.Text
    initialState = T.empty

    collectButtonPresses :: T.Text -> Button -> T.Text
    collectButtonPresses state buttonPress =
      case buttonPress of
        ButtonClear -> initialState
        ButtonNumber digit -> state <> digit

mondai :: 
  ( DomBuilder t m
  , Prerender t m
  , PostBuild t m
  ) => m (Dynamic t T.Text, Dynamic t T.Text) 
mondai = do
  monText <- prerender (return T.empty) $ liftIO $ reki 5
  let mon = fmap makeMon monText
      ans = fmap makeAns monText
      koto = fmap makeKoto monText
  divClass "kai" (dynText mon)
  blank
  return (ans,koto) 

makeAns :: T.Text -> T.Text
makeAns tx
  | tx==T.empty = T.empty
  | otherwise =
      let (_,ans) = T.breakOn "=" tx 
       in T.tail ans

makeMon :: T.Text -> T.Text
makeMon tx 
  | tx==T.empty = T.empty
  | otherwise = 
      let (erdata,_) = T.breakOn "=" tx 
       in  T.intercalate "\n" $
              zipWith (curry 
                (T.pack . (\(i,(_,d)) -> show i <> ": " <> T.unpack (T.tail d)))
                      ) [1::Int,2..] (map (T.breakOn "-") (T.splitOn "," erdata))    

makeKoto :: T.Text -> T.Text
makeKoto tx
  | tx==T.empty = T.empty
  | otherwise =
      let (erdata,_) = T.breakOn "=" tx 
       in  T.intercalate "\n" $
              map (T.pack . (\(n,d) -> show n <> "年: " <> d)) $
              sortNens $
              map ((\(ns,dt) -> ((read . T.unpack) ns,T.unpack (T.tail dt))) . 
                  T.breakOn "-") $
              T.splitOn "," erdata    

timer :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , TriggerEvent t m
  ) => m ()
timer = do
  tev <- tickLossyFromPostBuildTime 1 
  let tm = T.pack . show . (+1) . _tickInfo_n <$> tev
  dynText =<< holdDyn "start" tm 
  pure ()
  
charaAnime :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , TriggerEvent t m
  ) => m ()
charaAnime = do
  tev <- tickLossyFromPostBuildTime 1 
--  let tmi = (+1) . _tickInfo_n <$> tev
--  let tmText = T.pack . show <$> tmi
--  let tmChara = charaShow <$> tmi     
  dToggle <- toggle True tev
  let 
    dNotToggle = not <$> dToggle
    mkHidden False = "hidden" =: ""
    mkHidden True = mempty
    dHide1 = mkHidden <$> dToggle
    dHide2 = mkHidden <$> dNotToggle
--  dyi <- holdDyn "start" tmText 
--  el "p" $ dynText dyi
  el "p" $ text ""
  elDynAttr "div" dHide1 $ do chara0; timer
  elDynAttr "div" dHide2 $ do chara1; timer
--  widgetHold_ (charaShow 0) tmChara 
  pure ()
  
chara :: DomBuilder t m => m ()
chara = elAttr "img" ("src" =: $(static "chara0_mid.png")) blank

chara0 :: DomBuilder t m => m ()
chara0 = elAttr "img" ("src" =: $(static "chara0.png")) blank

chara1 :: DomBuilder t m => m ()
chara1 = elAttr "img" ("src" =: $(static "chara1.png")) blank

charaShow :: DomBuilder t m => Integer -> m ()
charaShow i = do
  let remain = rem i 2 
  case remain of 0 -> chara0; 1 -> chara1; _ -> chara0
