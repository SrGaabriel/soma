module Soma.Diagnostic where

import Data.List (nub)
import Data.Text (Text)
import Error.Diagnose (Marker (Where), Note (Note), Position (Position), Report (Err), TabSize (TabSize), WithUnicode (WithUnicode), addFile, addReport, stdout)
import Error.Diagnose.Diagnostic (printDiagnostic)
import Error.Diagnose.Style (defaultStyle)
import Maple.Position (Range (Range), Span (Span, spanTree), posRowCol)
import Soma.File (FileId, Files, SourceFile (SourceFile, srcContent, srcPath), lookupFile)

data Severity
    = SError
    | SWarning
    | SLint
    deriving (Show, Eq)

data Label = Label
    { labSpan :: Span
    , labMessage :: Text
    }
    deriving (Show, Eq)

data Diagnostic = Diagnostic
    { diagSeverity :: Severity
    , diagCode :: Maybe Text
    , diagMessage :: Text
    , diagPrimary :: Label
    , diagSecondaries :: [Label]
    , diagNotes :: [Text]
    , diagHelps :: [Text]
    }
    deriving (Show, Eq)

mkDiag :: Severity -> Text -> Label -> Diagnostic
mkDiag severity message primary =
    Diagnostic
        { diagSeverity = severity
        , diagCode = Nothing
        , diagMessage = message
        , diagPrimary = primary
        , diagSecondaries = []
        , diagNotes = []
        , diagHelps = []
        }

withCode :: Text -> Diagnostic -> Diagnostic
withCode code diag = diag{diagCode = Just code}

withSecondaries :: [Label] -> Diagnostic -> Diagnostic
withSecondaries secondaries diag = diag{diagSecondaries = secondaries}

withNotes :: [Text] -> Diagnostic -> Diagnostic
withNotes notes diag = diag{diagNotes = notes}

withHelps :: [Text] -> Diagnostic -> Diagnostic
withHelps helps diag = diag{diagHelps = helps}

withPrimary :: Label -> Diagnostic -> Diagnostic
withPrimary primary diag = diag{diagPrimary = primary}

addSecondary :: Label -> Diagnostic -> Diagnostic
addSecondary secondary diag = diag{diagSecondaries = diagSecondaries diag ++ [secondary]}

report :: Files -> Diagnostic -> IO ()
report files Diagnostic{diagMessage, diagCode, diagPrimary, diagSecondaries, diagHelps} =
    printDiagnostic stdout WithUnicode (TabSize 4) defaultStyle diagnostic
  where
    labels = diagPrimary : diagSecondaries
    sources = foldl' addSource mempty (nub (map labelFile labels))
    addSource d fileId = let SourceFile{srcPath, srcContent} = lookupFile files fileId in addFile d srcPath srcContent
    marker label@Label{labMessage} = (labelPosition files label, Where labMessage)
    diagnostic = addReport sources (Err diagCode diagMessage (map marker labels) (map Note diagHelps))

reportAll :: Files -> [Diagnostic] -> IO ()
reportAll files = mapM_ (report files)

labelFile :: Label -> FileId
labelFile = spanTree . labSpan

labelPosition :: Files -> Label -> Position
labelPosition files Label{labSpan = Span fileId (Range p1 p2)}
    | p1 == p2 = let (r, c) = posRowCol srcContent p1 in Position (r, c) (r, c + 1) srcPath
    | otherwise = Position (posRowCol srcContent p1) (posRowCol srcContent p2) srcPath
  where
    SourceFile{srcPath, srcContent} = lookupFile files fileId
