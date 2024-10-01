module Widget (elButtonMondai, elSpace, drawToCanvas) where

--import qualified JSDOM as DOM
import JSDOM
--import qualified GHCJS.DOM.Document as DOC
import qualified JSDOM.Types as DOM
import JSDOM.Custom.Window (scrollTo) 
import qualified JSDOM.Generated.NonElementParentNode as DOM
import qualified JSDOM.Generated.HTMLCanvasElement as Can 
--import qualified JSDOM.Generated.HTMLImageElement as Img
--import qualified JSDOM.Generated.Element as DOM
import JSDOM.Generated.Element(unElement) 
import qualified JSDOM.Generated.CanvasRenderingContext2D as DOM 
import Control.Monad.IO.Class (liftIO,MonadIO)
import Control.Monad.Fix (MonadFix)
import qualified Data.Text as T
import qualified Data.Map.Strict as Map

import Obelisk.Generated.Static (static)

import EReki (Rdt(..), reki, sortNens)

import Reflex.Dom.Core 
  ( text, dynText, el, elAttr, divClass, elAttr', blank, prerender_
  , (=:), leftmost, accumDyn, elDynAttr, elDynAttr', prerender 
  , holdDyn, domEvent, zipDynWith, zipDyn, current, gate, toggle
  , tickLossyFromPostBuildTime, widgetHold_ 
  , tag, constDyn, def, dropdown, value, sample
  , DomBuilder, Prerender, PerformEvent, TriggerEvent
  , PostBuild, Event, EventName(Click), MonadHold ,Dynamic
  , Performable, TickInfo(..)
  )

data Button = ButtonNumber T.Text | ButtonBack 

qNum :: Int
qNum = 5

mkHidden :: Bool -> Map.Map T.Text T.Text
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

--elChara :: DomBuilder t m => m ()
--elChara = elAttr "img" ("src" =: $(static "chara0_mid.png")) blank

monNums :: Map.Map Int T.Text
monNums = Map.fromList [(2,"2"),(3,"3"),(4,"4"),(5,"5"),(6,"6")
                       ,(7,"7"),(8,"8"),(9,"9"),(10,"10")]

monTypes :: Map.Map Int T.Text
monTypes = Map.fromList [(1,"通史"),(2,"近代史")]

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
  rec
    tb <- (elMondaiAction dyTM <$) <$> evElButton "pad2" "もんだい" 
    dyTypeNum <- dyDropDownNum monTypes 1
    dyMonNum <- dyDropDownNum monNums qNum
    let dyTM = zipDyn dyTypeNum dyMonNum
    elSpace 
    widgetHold_ (elMondaiAction dyTM) tb 
  pure ()

dyDropDownNum :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , PostBuild t m
  ) => Map.Map Int T.Text -> Int -> m (Dynamic t Int) 
dyDropDownNum selector dNum = do
    text ":--:"
    drChoiceNum <- dropdown dNum (constDyn selector) def
    let dyChoiceNum = value drChoiceNum
    return dyChoiceNum

elEvAllButtons :: (DomBuilder t m)  => Int -> m (Event t Button)
elEvAllButtons qn = do
  divClass "gr" $ do
    evNumberButtons <- evElNumberPad qn 
    evBackButton <- evElButton "pad" "B"
    let evButtons = leftmost [ ButtonBack <$ evBackButton
                             , ButtonNumber <$> evNumberButtons
                             ]
    return evButtons

elMondaiAction :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , Prerender t m
  , TriggerEvent t m
  ) => Dynamic t (Int,Int) -> m ()
elMondaiAction dyTM = do
  rec
    let beTM = current dyTM
    (tn,qn) <- sample beTM
    (dyAns,dyRdt) <- elMondai tn qn 
    dyTime <- elCharaAnime (fmap not dyIsAnsCorrect)
    let dyIsTime60 = 
          fmap (\ti -> (ti/="start") && (read . T.unpack) ti>(60::Int)) dyTime
    elSpace
    mapM_ (\n -> elOneMon dyIsTime60 (n+1) (fmap (getRdt n) dyRdt)) [0..(qn-1)]
    elSpace
    evButtons <- elEvAllButtons qn 
    dyState <- accumDyn collectButtonPresses initialState evButtons
    let dyIsAnsCorrect = zipDynWith (==) dyAns dyState
    el "p" $ dynText dyState
    elKai qn dyIsAnsCorrect dyRdt
  pure ()
  where
    initialState :: T.Text
    initialState = T.empty

    collectButtonPresses :: T.Text -> Button -> T.Text
    collectButtonPresses state buttonPress =
      case buttonPress of
        ButtonBack -> if state==T.empty then T.empty else T.init state 
        ButtonNumber digit -> state <> digit

evElButton :: (DomBuilder t m) => T.Text -> T.Text -> m (Event t ())
evElButton c s = do
  (e, _) <- elAttr' "button" ("type" =: "button" <> "class" =: c) $ text s
  let de = domEvent Click e
  return de 

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

evElNumberPad :: (DomBuilder t m) => Int -> m (Event t T.Text)
evElNumberPad i = do
  divClass "gr" $ do
    evts <- mapM (\n -> (toText n <$) <$> evElNumberButton (toText n)) [1..i] 
    let ev = leftmost evts
    return ev 
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
  ) => Int -> Dynamic t Bool -> Dynamic t [Rdt] -> m ()
elKai qn dyIsAnsCorrect dyRdt = do
  let dHide = mkHidden <$> dyIsAnsCorrect
  let dySRdt = fmap makeSort dyRdt
  elDynAttr "div" dHide $ mapM_ (\n -> elOneKai (fmap (getRdt n) dySRdt)) [0..(qn-1)]

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
  ) => Int -> Int -> m (Dynamic t T.Text, Dynamic t [Rdt]) 
elMondai tn qn = do
  dyRdtAns <- prerender (return ([],[])) $ liftIO $ reki tn qn 
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
--  widgetHold_ blank $ drawToCanvas <$ evTime
  holdDyn "start" evTimeText 
  
elCharaAnime :: 
  ( DomBuilder t m
  , MonadFix m
  , MonadHold t m
  , MonadIO (Performable m)
  , PerformEvent t m
  , PostBuild t m
  , Prerender t m
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
    dHideM = mkHidden . not <$> isAnsNotCorrect
  el "p" $ text ""
  elDynAttr "div" dHide1 $ do elChara0; dynText dyTime 
  elDynAttr "div" dHide2 $ do elChara1; dynText dyTime 
  elDynAttr "div" dHideM $ do
     evB <- (elScroll <$) <$> evElButton "pad3" "せいかい!!! ↓↓↓ "
     widgetHold_ elSpace evB
  pure dyTime 
  
elScroll :: (DomBuilder t m , Prerender t m) => m ()
elScroll = do
    prerender_ blank $ do
      win <- currentWindowUnchecked
      scrollTo win 0 1000 

--loadImage :: (DomBuilder t m, Prerender t m) => m () 
--loadImage = prerender_ blank $ do
--  doc <- currentDocumentUnchecked
--  img <- DOC.createElement doc ("img"::String)
--  let ie = DOM.HTMLImageElement (unElement img)
--  setId ie ("ch0"::String)
--  Img.setWidth ie 114
--  Img.setHeight ie 114
--  Img.setSrc ie ($(static "chara_mid.png")::String)


drawToCanvas :: (DomBuilder t m, Prerender t m) => m ()
drawToCanvas = prerender_ blank $ do
  doc <- currentDocumentUnchecked
  canvas <- DOM.getElementByIdUnchecked doc ("canvas" :: T.Text)
  let canvasElement = DOM.HTMLCanvasElement (unElement canvas)
  c <- Can.getContextUnchecked canvasElement ("2d"::String) ([] :: [DOM.JSString])
  let cx = DOM.CanvasRenderingContext2D (DOM.unRenderingContext c)
--  img <- DOC.createElement doc ("img"::String)
  img <- DOM.getElementByIdUnchecked doc ("ch0" :: String)
  let ie = DOM.HTMLImageElement (unElement img)
--  Img.setSrc ie ($(static "chara0.png") :: T.Text)
  let ci = DOM.CanvasImageSource $ DOM.unHTMLImageElement ie 
--  DOM.fillRect cx 10 10 100 100
  DOM.drawImage cx ci 0 0 
  DOM.setFont cx ("bold 23px serif"::T.Text)
  DOM.setFillStyle cx ("cyan"::String)
  DOM.fillText cx ("ふるい"::T.Text) 0 60 (Just 100) 
  DOM.strokeText cx ("ふるい"::T.Text) 0 60 (Just 100) 
  DOM.fillText cx ("じゅんに"::T.Text) 30 77 (Just 80) 
  DOM.strokeText cx ("じゅんに"::T.Text) 30 77 (Just 80) 
  DOM.fillText cx ("ならべて"::T.Text) 40 95 (Just 80) 
  DOM.strokeText cx ("ならべて"::T.Text) 40 95 (Just 80) 

elChara0 :: DomBuilder t m => m ()
elChara0 = elAttr "img" ("src" =: $(static "chara0.png")) blank

elChara1 :: DomBuilder t m => m ()
elChara1 = elAttr "img" ("src" =: $(static "chara1.png")) blank

