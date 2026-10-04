module Soma.Diagnostic where

import Data.Text (Text)
import Error.Diagnose (Marker (Where), Note (Note), Position (Position), Report (Err), TabSize (TabSize), WithUnicode (WithUnicode), addFile, addReport, stdout)
import Error.Diagnose.Diagnostic (printDiagnostic)
import Error.Diagnose.Style (defaultStyle)
import Maple.Position (Range (Range))
import Soma.File (SourceFile (SourceFile, srcContent, srcPath))

data Severity
    = SError
    | SWarning
    | SLint
    deriving (Show, Eq)

data Label = Label
    { labFile :: SourceFile
    , labRange :: Range
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

print :: Diagnostic -> IO ()
print
    ( Diagnostic
            { diagMessage
            , diagCode
            , diagSecondaries
            , diagPrimary =
                primary@Label
                    { labMessage = pMessage
                    , labFile = SourceFile{srcPath, srcContent}
                    }
            , diagHelps
            }
        ) =
        let positions =
                (labelPosition primary, Where pMessage)
                    : map
                        (\label@Label{labMessage} -> (labelPosition label, Where labMessage))
                        diagSecondaries
            helps = map Note diagHelps
            report =
                Err
                    diagCode
                    diagMessage
                    positions
                    helps
            diagnostic = addFile mempty srcPath srcContent
            diagnostic' = addReport diagnostic report
        in printDiagnostic stdout WithUnicode (TabSize 4) defaultStyle diagnostic'

labelPosition :: Label -> Position
labelPosition Label{labFile = SourceFile{srcPath}, labRange = (Range p1 p2)} = Position (2, 3) (5, 6) srcPath
