module Soma.Text where

import qualified Data.Text as T

safeIndex :: T.Text -> Int -> Maybe Char
safeIndex t i
    | i < 0 || i >= T.length t = Nothing
    | otherwise = Just (T.index t i)
