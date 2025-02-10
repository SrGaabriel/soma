module Logging.ErrorPrinter (printError) where

import Data.List (findIndex)
import Data.Maybe (fromMaybe)
import System.Console.ANSI

data RowInfo = RowInfo
  { content :: String
  , relativeIndex :: Int
  , number :: Int
  }

printError :: FilePath -> String -> String -> Int -> Int -> String -> IO ()
printError fileName code prefix start end message = do
  case findRowOfIndex (lines code) start of
    Just rowInfo -> do
      let (contentTrim, trimWidth) = trimIndentReturningWidth (content rowInfo)
          relativeStart = relativeIndex rowInfo - trimWidth
          relativeEnd = min
            (relativeIndex rowInfo + errorLength - trimWidth)
            (Prelude.length contentTrim)
          textToHighlight = take (relativeEnd - relativeStart) $ drop relativeStart contentTrim
          positionIndicator = replicate relativeStart ' ' ++ replicate (relativeEnd - relativeStart + 1) '^'
          
      -- First line with error message
      setSGR [SetColor Foreground Vivid Red]
      putStr $ fileName ++ ":" ++ show (number rowInfo) ++ ":" ++ show (relativeStart + 1) ++ " "
      setSGR [Reset]
      setSGR [SetConsoleIntensity BoldIntensity]
      putStr $ "[" ++ prefix ++ "] "
      setSGR [SetColor Foreground Vivid Red]
      setSGR [SetConsoleIntensity BoldIntensity]
      putStr "error: "
      setSGR [SetColor Foreground Dull White]
      setSGR [SetConsoleIntensity NormalIntensity]
      putStrLn message
      setSGR [Reset]
      
      -- Separator line
      putStrLn "|"
      
      -- Code line
      putStr "| row: "
      putStr (take relativeStart contentTrim)
      setSGR [SetColor Foreground Vivid Red]
      putStr textToHighlight
      setSGR [Reset]
      let textLength = length textToHighlight
      putStrLn (drop (relativeStart + textLength) contentTrim)
      
      -- Position indicator line
      putStr $ "| pos: "
      setSGR [SetColor Foreground Vivid Red]
      putStrLn positionIndicator

      
    Nothing -> error "Error while finding the line of the error"
  where
    errorLength = end - start

findRowOfIndex :: [String] -> Int -> Maybe RowInfo
findRowOfIndex rows index = do
  let codeContent = unlines rows
  if index < 0 || index >= length codeContent
    then Nothing
    else do
      let rowStartIndex = lastIndexOf '\n' codeContent (index - 1)
          rowEndIndex = findIndex (=='\n') $ drop index codeContent
          actualRowEndIndex = maybe (length codeContent) (+index) rowEndIndex
          rowContent = take (actualRowEndIndex - rowStartIndex - 1) $ drop (rowStartIndex + 1) codeContent
          relativeIndexInRow = index - (rowStartIndex + 1)
          rowNumber = length (filter (=='\n') $ take index codeContent) + 1
      Just $ RowInfo rowContent relativeIndexInRow rowNumber

trimIndentReturningWidth :: String -> (String, Int)
trimIndentReturningWidth str =
  let width = fromMaybe (length str) $ findIndex (not . isSpace) str
  in (drop width str, width)

-- Helper for finding last index of character
lastIndexOf :: Char -> String -> Int -> Int
lastIndexOf c str maxIndex = go (min maxIndex (length str - 1))
  where
    go i
      | i < 0 = -1
      | str !! i == c = i
      | otherwise = go (i - 1)

isSpace :: Char -> Bool
isSpace c = c == ' ' || c == '\t' || c == '\n' || c == '\r'