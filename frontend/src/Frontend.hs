module Frontend where

--import Common.Api (commonStuff)
import Common.Route (FrontendRoute (..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Fix (MonadFix)
import qualified Data.Text as T
import Obelisk.Frontend (Frontend (..))
import Obelisk.Route (R)
import Obelisk.Generated.Static (static)

import Reflex.Dom.Core 
  ( text, el, elAttr, blank , (=:), divClass
  , DomBuilder, Prerender, PerformEvent, TriggerEvent
  , PostBuild, MonadHold , Performable
  )

import Widget (elButtonMondai, elSpace, drawToCanvas)


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
--  el "p" $ text $ T.pack commonStuff
  elAttr "canvas" ("id" =: "canvas" <> "width" =: "130" <> "height" =: "115") blank
--  divClass "res" $
  elAttr "img" ("id" =: "ch0" <> "width" =: "114" <> "height" =: "114" <> "src" =: $(static "chara_mid.png")) blank
  drawToCanvas
  elSpace
  elButtonMondai 
  elSpace

