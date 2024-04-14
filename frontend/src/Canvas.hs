module Canvas (elCanvas) where

import Reflex.Dom.Core (elAttr,blank,(=:),DomBuilder)
--import Obelisk.Generated.Static (static)
--import JSDOM.Types (MonadDOM,ToJSString,IsElement)
--import GHCJS.DOM.Document (newDocument,createElement,IsDocument)
--import JSDOM.Generated.HTMLCanvasElement (getContext)

{-
elCanvas :: 
  ( MonadDOM m
  , IsDocument self
  , ToJSString localName
  ) => m ()
elCanvas = do
  doc <- newDocument
  elm <- createElement doc "canvas"
  Just cx <- getContext elm "2d" []
-}  

elCanvas :: DomBuilder t m => m ()
elCanvas = do
  elAttr 
    "canvas"
    ( "id" =: "eCanvas"
      <> "style" =: "border: 1px solid khaki; background-color: #008080"
      <> "width" =: "114"
      <> "height" =: "114"
    )
    blank
