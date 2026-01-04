module Ide.Vfs.Change (
    TextChange (..),
    applyChange,
    applyChanges,
    insertText,
    deleteRange,
    replaceRange,
    affectedRange,
    adjustOffset,
) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word32)
import Syntax.CST.GreenTree (TextRange (..))

data TextChange
    = TextChange
    { tcRange :: !TextRange -- range to replace (empty for insertion)
    , tcNewText :: !Text
    }
    deriving (Eq, Show)

applyChange :: TextChange -> Text -> Text
applyChange (TextChange (TextRange start len) newText) txt =
    let (before, rest) = T.splitAt (fromIntegral start) txt
        after = T.drop (fromIntegral len) rest
    in before <> newText <> after

applyChanges :: [TextChange] -> Text -> Text
applyChanges changes txt = foldr applyChange txt changes

insertText :: Word32 -> Text -> TextChange
insertText offset = TextChange (TextRange offset 0)

deleteRange :: TextRange -> TextChange
deleteRange range = TextChange range T.empty

replaceRange :: TextRange -> Text -> TextChange
replaceRange = TextChange

affectedRange :: TextChange -> TextRange
affectedRange (TextChange range _) = range

adjustOffset :: TextChange -> Word32 -> Maybe Word32
adjustOffset (TextChange (TextRange start len) newText) offset
    | offset < start = Just offset
    | offset < start + len = Nothing
    | otherwise = Just $ offset - len + fromIntegral (T.length newText)
