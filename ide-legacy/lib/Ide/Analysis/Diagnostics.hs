module Ide.Analysis.Diagnostics (
    Diagnostic (..),
    DiagnosticSeverity (..),
    DiagnosticTag (..),
    DiagnosticRelated (..),
    collectSyntaxDiagnostics,
    collectTypeDiagnostics,
    collectAllDiagnostics,
    formatDiagnostic,
    severityToText,
) where

import Data.List (group, sort)
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Ide.Analysis.Definition qualified as D
import Syntax.CST.GreenTree (TextRange (..), gtKind, gtText, ndKind, ndTextLen, unGreenNode)
import Syntax.CST.RedTree
import Syntax.CST.SyntaxKind

data DiagnosticSeverity
    = SeverityError
    | SeverityWarning
    | SeverityInfo
    | SeverityHint
    deriving (Eq, Ord, Show)

data DiagnosticTag
    = TagUnnecessary
    | TagDeprecated
    deriving (Eq, Show)

data DiagnosticRelated = DiagnosticRelated
    { drRange :: !TextRange
    , drMessage :: !Text
    }
    deriving (Eq, Show)

data Diagnostic = Diagnostic
    { diagRange :: !TextRange
    , diagSeverity :: !DiagnosticSeverity
    , diagCode :: !(Maybe Text)
    , diagSource :: !Text
    , diagMessage :: !Text
    , diagTags :: ![DiagnosticTag]
    , diagRelated :: ![DiagnosticRelated]
    }
    deriving (Eq, Show)

collectSyntaxDiagnostics :: SyntaxNode -> [Diagnostic]
collectSyntaxDiagnostics syNode =
    let nodeDiags = checkNode syNode
        childDiags = concatMap collectSyntaxDiagnostics (children syNode)
    in nodeDiags ++ childDiags
  where
    checkNode :: SyntaxNode -> [Diagnostic]
    checkNode n
        | isError (ndKind (unGreenNode (snGreen n))) =
            [ Diagnostic
                { diagRange = TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
                , diagSeverity = SeverityError
                , diagCode = Just "E0001"
                , diagSource = "soma/syntax"
                , diagMessage = "Syntax error: unexpected token"
                , diagTags = []
                , diagRelated = []
                }
            ]
        | otherwise = checkSyntaxRules n

    checkSyntaxRules :: SyntaxNode -> [Diagnostic]
    checkSyntaxRules n = case ndKind (unGreenNode (snGreen n)) of
        SK_Node NK_BINDING_DEF -> checkBindingDef n
        SK_Node NK_DATA_DEF -> checkDataDef n
        SK_Node NK_IMPORT_DECL -> checkImport n
        SK_Node NK_EXPR_VAR -> checkUnresolvedVar n
        _ -> []

    checkBindingDef :: SyntaxNode -> [Diagnostic]
    checkBindingDef n =
        let hasTypeSig = any (\c -> ndKind (unGreenNode (snGreen c)) == SK_Node NK_TYPE_SIGNATURE) (children n)
        in ( [ Diagnostic
                { diagRange = TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
                , diagSeverity = SeverityWarning
                , diagCode = Just "W0001"
                , diagSource = "soma/syntax"
                , diagMessage = "Missing type signature"
                , diagTags = []
                , diagRelated = []
                }
             | not hasTypeSig
             ]
           )

    checkDataDef :: SyntaxNode -> [Diagnostic]
    checkDataDef n =
        let constructors = childrenOfKind (SK_Node NK_DATA_CONSTRUCTOR) n
            emptyCheck = checkNoConstructors n constructors
            duplicateCtorCheck = checkDuplicateConstructors constructors
            fieldChecks = concatMap checkConstructorFields constructors
        in emptyCheck ++ duplicateCtorCheck ++ fieldChecks

    checkNoConstructors :: SyntaxNode -> [SyntaxNode] -> [Diagnostic]
    checkNoConstructors n constructors
        | null constructors =
            [ Diagnostic
                { diagRange = TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
                , diagSeverity = SeverityWarning
                , diagCode = Just "W0002"
                , diagSource = "soma/syntax"
                , diagMessage = "Data type has no constructors"
                , diagTags = []
                , diagRelated = []
                }
            ]
        | otherwise = []

    checkDuplicateConstructors :: [SyntaxNode] -> [Diagnostic]
    checkDuplicateConstructors constructors =
        let names = mapMaybe getConstructorName constructors
            duplicates = filter ((> 1) . length) . group . sort $ map fst names
        in concatMap (makeDuplicateDiag "Constructor") duplicates

    checkConstructorFields :: SyntaxNode -> [Diagnostic]
    checkConstructorFields ctor =
        let fields = childrenOfKind (SK_Node NK_CONSTRUCTOR_FIELD) ctor
            names = mapMaybe getFieldName fields
            duplicates = filter ((> 1) . length) . group . sort $ map fst names
        in concatMap (makeDuplicateDiag "Field") duplicates

    getConstructorName :: SyntaxNode -> Maybe (Text, SyntaxNode)
    getConstructorName n = do
        tok <- firstToken n
        case gtKind (stGreen tok) of
            SK_Token TokenUpperIdentifier -> Just (gtText (stGreen tok), n)
            _ -> Nothing

    getFieldName :: SyntaxNode -> Maybe (Text, SyntaxNode)
    getFieldName n = do
        tok <- firstToken n
        case gtKind (stGreen tok) of
            SK_Token TokenLowerIdentifier -> Just (gtText (stGreen tok), n)
            _ -> Nothing

    makeDuplicateDiag :: Text -> [Text] -> [Diagnostic]
    makeDuplicateDiag kind names = case names of
        (name : _) ->
            [ Diagnostic
                { diagRange = TextRange 0 0
                , diagSeverity = SeverityError
                , diagCode = Just "E0002"
                , diagSource = "soma/syntax"
                , diagMessage = kind <> " '" <> name <> "' is defined multiple times"
                , diagTags = []
                , diagRelated = []
                }
            ]
        [] -> []

    checkImport :: SyntaxNode -> [Diagnostic]
    checkImport n =
        let hasModulePath = any isModulePathElement (childrenWithTokens n)
            pathCheck =
                ( [ Diagnostic
                        { diagRange = TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
                        , diagSeverity = SeverityError
                        , diagCode = Just "E0003"
                        , diagSource = "soma/syntax"
                        , diagMessage = "Import declaration missing module path"
                        , diagTags = []
                        , diagRelated = []
                        }
                  | not hasModulePath
                  ]
                )
            importListCheck = maybe [] checkImportList (childOfKind (SK_Node NK_IMPORT_LIST) n)
        in pathCheck ++ importListCheck

    isModulePathElement :: SyntaxElement -> Bool
    isModulePathElement (SyntaxNodeElement node) =
        ndKind (unGreenNode (snGreen node)) == SK_Node NK_QUALIFIED_NAME
    isModulePathElement (SyntaxTokenElement tok) =
        gtKind (stGreen tok) == SK_Token TokenLowerIdentifier

    checkImportList :: SyntaxNode -> [Diagnostic]
    checkImportList importList =
        let items = children importList
            emptyCheck =
                ( [ Diagnostic
                        { diagRange = TextRange (snOffset importList) (ndTextLen (unGreenNode (snGreen importList)))
                        , diagSeverity = SeverityWarning
                        , diagCode = Just "W0003"
                        , diagSource = "soma/syntax"
                        , diagMessage = "Empty import list"
                        , diagTags = [TagUnnecessary]
                        , diagRelated = []
                        }
                  | null items
                  ]
                )
        in emptyCheck

    checkUnresolvedVar :: SyntaxNode -> [Diagnostic]
    checkUnresolvedVar n =
        case firstToken n of
            Nothing -> []
            Just tok ->
                let name = gtText (stGreen tok)
                in if isBuiltin name
                    then []
                    else case D.resolveSymbol syNode tok of
                        D.Unresolved ->
                            [ Diagnostic
                                { diagRange = TextRange (stOffset tok) (fromIntegral $ T.length name)
                                , diagSeverity = SeverityError
                                , diagCode = Just "E0004"
                                , diagSource = "soma/resolve"
                                , diagMessage = "Unresolved variable: " <> name
                                , diagTags = []
                                , diagRelated = []
                                }
                            ]
                        _ -> []

    isBuiltin :: Text -> Bool
    isBuiltin name = name `elem` ["true", "false", "unit"]

collectTypeDiagnostics :: SyntaxNode -> [Diagnostic]
collectTypeDiagnostics root = concatMap checkDecl (children root)
  where
    checkDecl n = case ndKind (unGreenNode (snGreen n)) of
        SK_Node NK_BINDING_DEF -> checkBindingTypes n
        SK_Node NK_DATA_DEF -> checkDataTypes n
        SK_Node NK_TRAIT_DEF -> checkTraitTypes n
        _ -> []

    checkBindingTypes :: SyntaxNode -> [Diagnostic]
    checkBindingTypes n =
        maybe
            []
            checkTypeSignature
            (childOfKind (SK_Node NK_TYPE_SIGNATURE) n)

    checkTypeSignature :: SyntaxNode -> [Diagnostic]
    checkTypeSignature sig =
        let typeNodes = childrenOfKind (SK_Node NK_TYPE) sig
            forallNode = childOfKind (SK_Node NK_FORALL) sig
            duplicateTyVars = maybe [] checkDuplicateTyVars forallNode
        in concatMap checkTypeExpr typeNodes ++ duplicateTyVars

    checkTypeExpr :: SyntaxNode -> [Diagnostic]
    checkTypeExpr n = case ndKind (unGreenNode (snGreen n)) of
        SK_Node NK_TYPE_APP -> checkTypeApp n
        _ -> []

    checkTypeApp :: SyntaxNode -> [Diagnostic]
    checkTypeApp n =
        let typeChildren = children n
        in case typeChildren of
            [] ->
                [ Diagnostic
                    { diagRange = TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
                    , diagSeverity = SeverityError
                    , diagCode = Just "E0010"
                    , diagSource = "soma/type"
                    , diagMessage = "Empty type application"
                    , diagTags = []
                    , diagRelated = []
                    }
                ]
            _ -> concatMap checkTypeExpr typeChildren

    checkDuplicateTyVars :: SyntaxNode -> [Diagnostic]
    checkDuplicateTyVars forallNode =
        let tyVarNodes = childrenOfKind (SK_Node NK_TYPE_VAR) forallNode
            names = mapMaybe getTyVarName tyVarNodes
            duplicates = filter ((> 1) . length) . group . sort $ names
        in concatMap makeDupTyVarDiag duplicates
      where
        getTyVarName n = gtText . stGreen <$> firstToken n
        makeDupTyVarDiag names = case names of
            (name : _) ->
                [ Diagnostic
                    { diagRange = TextRange (snOffset forallNode) (ndTextLen (unGreenNode (snGreen forallNode)))
                    , diagSeverity = SeverityError
                    , diagCode = Just "E0011"
                    , diagSource = "soma/type"
                    , diagMessage = "Duplicate type variable '" <> name <> "'"
                    , diagTags = []
                    , diagRelated = []
                    }
                ]
            [] -> []

    checkDataTypes :: SyntaxNode -> [Diagnostic]
    checkDataTypes n =
        let tyVarNodes = filter isTyVar (children n)
            names = mapMaybe getTyVarName tyVarNodes
            duplicates = filter ((> 1) . length) . group . sort $ names
        in concatMap makeDupTyVarDiag duplicates
      where
        isTyVar node = ndKind (unGreenNode (snGreen node)) == SK_Node NK_TYPE_VAR
        getTyVarName node = gtText . stGreen <$> firstToken node
        makeDupTyVarDiag names = case names of
            (name : _) ->
                [ Diagnostic
                    { diagRange = TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
                    , diagSeverity = SeverityError
                    , diagCode = Just "E0011"
                    , diagSource = "soma/type"
                    , diagMessage = "Duplicate type parameter '" <> name <> "'"
                    , diagTags = []
                    , diagRelated = []
                    }
                ]
            [] -> []

    checkTraitTypes :: SyntaxNode -> [Diagnostic]
    checkTraitTypes n =
        maybe
            [ Diagnostic
                { diagRange =
                    TextRange
                        (snOffset n)
                        (ndTextLen (unGreenNode (snGreen n)))
                , diagSeverity = SeverityError
                , diagCode = Just "E0012"
                , diagSource = "soma/type"
                , diagMessage = "Trait definition missing type signature"
                , diagTags = []
                , diagRelated = []
                }
            ]
            checkTypeSignature
            (childOfKind (SK_Node NK_TYPE_SIGNATURE) n)

collectAllDiagnostics :: SyntaxNode -> [Diagnostic]
collectAllDiagnostics root =
    collectSyntaxDiagnostics root ++ collectTypeDiagnostics root

formatDiagnostic :: Diagnostic -> Text
formatDiagnostic d =
    T.concat
        [ severityToText (diagSeverity d)
        , maybe "" (\c -> "[" <> c <> "] ") (diagCode d)
        , diagMessage d
        ]

severityToText :: DiagnosticSeverity -> Text
severityToText SeverityError = "error: "
severityToText SeverityWarning = "warning: "
severityToText SeverityInfo = "info: "
severityToText SeverityHint = "hint: "
