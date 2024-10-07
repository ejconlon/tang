module Tang.Render where

import Control.Monad.State.Strict (State, modify', runState)
import Data.Foldable (foldl')
import Data.Text (Text)
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as TLB
import Data.Text.Lazy.IO qualified as TLIO

newtype RenderM a = RenderM {unRenderM :: State Builder a}
  deriving newtype (Functor, Applicative, Monad)

runRenderM :: RenderM a -> Builder -> (a, Builder)
runRenderM = runState . unRenderM

simpleEvalRenderM :: RenderM () -> Text
simpleEvalRenderM = TL.toStrict . TLB.toLazyText . snd . flip runRenderM mempty

fileEvalRenderM :: FilePath -> RenderM () -> IO ()
fileEvalRenderM fp = TLIO.writeFile fp . TLB.toLazyText . snd . flip runRenderM mempty

renderBuilder :: Builder -> RenderM ()
renderBuilder = RenderM . modify' . (<>)

renderBuilders :: [Builder] -> RenderM ()
renderBuilders xs = RenderM (modify' (\b -> foldl' (<>) b xs))

renderText :: Text -> RenderM ()
renderText = renderBuilder . TLB.fromText

renderTexts :: [Text] -> RenderM ()
renderTexts ts = RenderM (modify' (\b0 -> foldl' (\b t -> b <> TLB.fromText t) b0 ts))

fromShowable :: (Show a) => a -> Builder
fromShowable = TLB.fromString . show
