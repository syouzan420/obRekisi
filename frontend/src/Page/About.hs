{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module Page.About (page) where

--import Common.Route (FrontendRoute)
--import Control.Monad.Fix (MonadFix)
--import Obelisk.Route.Frontend (R, Routed, SetRoute)
import Reflex.Dom.Core

page ::
  DomBuilder t m => m ()
page = do
  el "p" $ text "created by yokoP"
  
  
