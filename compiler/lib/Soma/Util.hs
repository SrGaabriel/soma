module Soma.Util where

import qualified Data.Text as T

safeIndex :: T.Text -> Int -> Maybe Char
safeIndex t i
    | i < 0 || i >= T.length t = Nothing
    | otherwise = Just (T.index t i)

maybeM :: (Monad m) => b -> (a -> m b) -> m (Maybe a) -> m b
maybeM def f action = do
    val <- action
    case val of
        Nothing -> pure def
        Just x -> f x
