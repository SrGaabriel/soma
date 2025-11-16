module Logging.ErrorPrinter (PrintableError (..), printError, printConclusionMessage) where

import Control.Monad (when)
import Data.List (elemIndex, findIndex)
import Data.Maybe (fromMaybe)
import Logging.Errors (PrintableError (..))
import System.Console.ANSI
import System.IO (hPutStr, hPutStrLn, stderr)

data RowInfo = RowInfo
    { content :: String
    , relativeIndex :: Int
    , number :: Int
    }

printConclusionMessage :: String -> IO ()
printConclusionMessage message = do
    ePutStrLn ""
    setSGR [SetConsoleIntensity BoldIntensity]
    setSGR [SetColor Foreground Vivid Red]
    setSGR [SetConsoleIntensity BoldIntensity]
    ePutStr "OUTPUT: "
    setSGR [SetColor Foreground Dull White]
    setSGR [SetConsoleIntensity NormalIntensity]
    ePutStrLn message
    setSGR [Reset]

printError :: (PrintableError a) => a -> FilePath -> String -> String -> IO ()
printError err fileName code prefix = do
    let isNewline = start < length code && code !! start == '\n'
        adjustedStart = if isNewline then start + 1 else start
        adjustedEnd =
            if isNewline
                then case elemIndex '\n' $ drop (start + 1) code of
                    Just nextNewline -> start + 1 + nextNewline
                    Nothing -> length code
                else end

    case findRowOfIndex (lines code) adjustedStart of
        Just rowInfo -> do
            let (contentTrim, trimWidth) = trimIndentReturningWidth (content rowInfo)
                relativeStart =
                    if isNewline
                        then 0
                        else max 0 (relativeIndex rowInfo - trimWidth)
                relativeEnd =
                    if isNewline
                        then length contentTrim
                        else
                            min
                                (relativeIndex rowInfo + (adjustedEnd - adjustedStart) - trimWidth)
                                (length contentTrim)
                textLength = relativeEnd - relativeStart
                textToHighlight = take textLength $ drop relativeStart contentTrim
                positionIndicator = replicate relativeStart ' ' ++ replicate textLength '^'

            setSGR [SetColor Foreground Vivid Red]
            ePutStr $ fileName ++ ":" ++ show (number rowInfo) ++ ":" ++ show (relativeIndex rowInfo + 1) ++ " "
            setSGR [Reset]

            setSGR [SetConsoleIntensity BoldIntensity]
            ePutStr $ "[" ++ prefix ++ "] "
            setSGR [SetColor Foreground Vivid Red]
            setSGR [SetConsoleIntensity BoldIntensity]
            ePutStr "error: "
            setSGR [SetColor Foreground Dull White]
            setSGR [SetConsoleIntensity NormalIntensity]
            ePutStrLn message
            setSGR [Reset]

            ePutStrLn "|"

            ePutStr "| row: "
            if contentTrim == ""
                then ePutStrLn "<empty row>"
                else do
                    ePutStr (take relativeStart contentTrim)
                    setSGR [SetColor Foreground Vivid Red]
                    ePutStr textToHighlight
                    setSGR [Reset]
                    ePutStrLn (drop (relativeStart + textLength) contentTrim)

            when (textLength > 0) $ do
                ePutStr "| pos: "
                setSGR [SetColor Foreground Vivid Red]
                ePutStrLn positionIndicator

            setSGR [Reset]
            ePutStrLn $ "| debug: " ++ errorDebugDevDetails err
        Nothing ->
            error $ "Error while finding the line of the error: " ++ errorMessage err
  where
    start' = errorStart err
    end' = errorEnd err
    (start, end) =
        if start' < 0 && end' < 0
            then let codeLength = length code in (codeLength, codeLength)
            else (start', end')
    message = errorMessage err

findRowOfIndex :: [String] -> Int -> Maybe RowInfo
findRowOfIndex rows idx = do
    if idx == -1 && not (null rows)
        then Just $ RowInfo "" 0 (length rows)
        else do
            let codeContent = unlines rows
                fixedIndex =
                    if idx >= length codeContent && not (null codeContent)
                        then length codeContent - 1
                        else idx

            if fixedIndex < 0 || fixedIndex >= length codeContent
                then Nothing
                else do
                    let rowStartIndex = lastIndexOf '\n' codeContent (fixedIndex - 1)
                        rowEndIndex = elemIndex '\n' $ drop fixedIndex codeContent
                        actualRowEndIndex =
                            maybe (length codeContent) (+ fixedIndex) rowEndIndex

                        rowContent =
                            take (actualRowEndIndex - rowStartIndex - 1)
                                $ drop (rowStartIndex + 1) codeContent

                        relativeIndexInRow = fixedIndex - (rowStartIndex + 1)
                        rowNumber =
                            length (filter (== '\n') $ take fixedIndex codeContent) + 1

                    Just $ RowInfo rowContent relativeIndexInRow rowNumber

trimIndentReturningWidth :: String -> (String, Int)
trimIndentReturningWidth str =
    let width = fromMaybe (length str) (findIndex (/= ' ') str)
    in (drop width str, width)

lastIndexOf :: Char -> String -> Int -> Int
lastIndexOf c str maxIndex = go (min maxIndex (length str - 1))
  where
    go i
        | i < 0 = -1
        | str !! i == c = i
        | otherwise = go (i - 1)

ePutStr :: String -> IO ()
ePutStr = hPutStr stderr

ePutStrLn :: String -> IO ()
ePutStrLn = hPutStrLn stderr
