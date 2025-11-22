module Souls.Logging where
import Data.Text.IO (hPutStrLn)
import System.IO (stderr)
import qualified Data.Text as T

logToClient :: String -> IO ()
logToClient msg = hPutStrLn stderr (T.pack $ "[Server Log] " ++ msg)