module Logging.ErrorPrinter (PrintableError(..), printError) where

import Data.List (findIndex)
import Data.Maybe (fromMaybe)
import System.Console.ANSI

class PrintableError a where
    errorMessage :: a -> String
    errorStart :: a -> Int
    errorEnd :: a -> Int

data RowInfo = RowInfo
  { content :: String
  , relativeIndex :: Int
  , number :: Int
  }

printError :: PrintableError a => a -> FilePath -> String -> String -> IO ()
printError err fileName code prefix = do
  case findRowOfIndex (lines code) start of
    Just rowInfo -> do
      let (contentTrim, trimWidth) = trimIndentReturningWidth (content rowInfo)
          relativeStart = relativeIndex rowInfo - trimWidth
          relativeEnd = min
            (relativeIndex rowInfo + errorLength - trimWidth)
            (Prelude.length contentTrim)
          textToHighlight = take (relativeEnd - relativeStart + 1) $ drop relativeStart contentTrim
          positionIndicator = replicate relativeStart ' ' ++ replicate (relativeEnd - relativeStart + 1) '^'
          
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
      
      putStrLn "|"
      
      putStr "| row: "
      putStr (take relativeStart contentTrim)
      setSGR [SetColor Foreground Vivid Red]
      putStr textToHighlight
      setSGR [Reset]
      let textLength = length textToHighlight
      putStrLn (drop (relativeStart + textLength) contentTrim)
      
      putStr $ "| pos: "
      setSGR [SetColor Foreground Vivid Red]
      putStrLn positionIndicator

      
    Nothing -> error "Error while finding the line of the error"
  where
    start = errorStart err
    end = errorEnd err
    message = errorMessage err
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
  let width = fromMaybe (length str) $ findIndex (/= ' ') str
  in (drop width str, width)

lastIndexOf :: Char -> String -> Int -> Int
lastIndexOf c str maxIndex = go (min maxIndex (length str - 1))
  where
    go i
      | i < 0 = -1
      | str !! i == c = i
      | otherwise = go (i - 1)

