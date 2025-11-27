module Ide.Query.Queries (
    FileId,
    fileId,
    fileIdPath,
    sourceText,
    setSourceText,
    parsedFile,
    syntaxTree,
    fileSymbols,
    resolvedNames,
    fileImports,
    moduleExports,
    inferredTypes,
    symbolType,
    expressionType,
    fileDiagnostics,
    allDiagnostics,
    definitionLocation,
    references,
    hover,
    completions,
    QueryContext (..),
    newQueryContext,
    newQueryContextWithResolver,
    updateFile,
    removeFile,
    resolveModuleName,
    resolveFilePath,
) where

import Control.Concurrent.STM
import Data.HashMap.Strict qualified as HM
import Data.Hashable (Hashable (..))
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word32)
import GHC.Generics (Generic)
import Ide.Analysis.Completion qualified as C
import Ide.Analysis.Definition qualified as D
import Ide.Analysis.Diagnostics qualified as Diag
import Ide.Analysis.Hover qualified as H
import Ide.Project.Resolve (ModuleResolver, ResolvedModule (..))
import Ide.Project.Resolve qualified as R
import Ide.Query.Database
import Ide.Query.Durability
import Ide.Syntax.Parse (parseSourceFile)
import Syntax.CST.GreenTree
import Syntax.CST.RedTree
import Syntax.CST.SyntaxKind

newtype FileId = FileId {unFileId :: Text}
    deriving (Eq, Ord, Show, Generic)

instance Hashable FileId where
    hashWithSalt s (FileId t) = hashWithSalt s t

fileId :: FilePath -> FileId
fileId = FileId . T.pack

fileIdPath :: FileId -> FilePath
fileIdPath = T.unpack . unFileId

data QueryContext = QueryContext
    { qcDatabase :: !Database
    , qcFileInputs :: !(TVar (HM.HashMap FileId InputId))
    , qcInterner :: !GreenInterner
    , qcResolver :: !(TVar (Maybe ModuleResolver))
    }

newQueryContext :: IO QueryContext
newQueryContext =
    QueryContext
        <$> newDatabase
        <*> newTVarIO HM.empty
        <*> newInterner
        <*> newTVarIO Nothing

newQueryContextWithResolver :: ModuleResolver -> IO QueryContext
newQueryContextWithResolver resolver =
    QueryContext
        <$> newDatabase
        <*> newTVarIO HM.empty
        <*> newInterner
        <*> newTVarIO (Just resolver)

updateFile :: QueryContext -> FileId -> Text -> IO ()
updateFile ctx fid content = do
    fileInputs <- readTVarIO (qcFileInputs ctx)
    case HM.lookup fid fileInputs of
        Just _existing -> do
            _ <- setInputWithDurability (qcDatabase ctx) Low content
            return ()
        Nothing -> do
            newId <- setInputWithDurability (qcDatabase ctx) Low content
            atomically $ modifyTVar' (qcFileInputs ctx) (HM.insert fid newId)

removeFile :: QueryContext -> FileId -> IO ()
removeFile ctx fid =
    atomically
        $ modifyTVar' (qcFileInputs ctx) (HM.delete fid)

sourceText :: QueryContext -> FileId -> IO (Maybe Text)
sourceText ctx fid = do
    fileInputs <- readTVarIO (qcFileInputs ctx)
    case HM.lookup fid fileInputs of
        Nothing -> return Nothing
        Just inputId -> getInput (qcDatabase ctx) inputId

setSourceText :: QueryContext -> FileId -> Text -> IO ()
setSourceText = updateFile

parsedFile :: QueryContext -> FileId -> IO (Maybe GreenNode)
parsedFile ctx fid = do
    query (qcDatabase ctx) "parsedFile" fid $ \tracker fid' -> do
        fileInputs <- readTVarIO (qcFileInputs ctx)
        case HM.lookup fid' fileInputs of
            Nothing -> return Nothing
            Just inputId -> do
                trackDependency tracker inputId
                mText <- getInput (qcDatabase ctx) inputId
                case mText of
                    Nothing -> return Nothing
                    Just txt -> Just <$> parseToGreenTree (qcInterner ctx) txt

syntaxTree :: QueryContext -> FileId -> IO (Maybe SyntaxNode)
syntaxTree ctx fid = do
    mGreen <- parsedFile ctx fid
    return $ syntaxRoot <$> mGreen

parseToGreenTree :: GreenInterner -> Text -> IO GreenNode
parseToGreenTree = parseSourceFile

resolveModuleName :: QueryContext -> Text -> IO (Maybe FilePath)
resolveModuleName ctx modName = do
    mResolver <- readTVarIO (qcResolver ctx)
    return $ mResolver >>= \r -> R.resolveModuleToPath r modName

resolveFilePath :: QueryContext -> FilePath -> IO (Maybe ResolvedModule)
resolveFilePath ctx path = do
    mResolver <- readTVarIO (qcResolver ctx)
    return $ mResolver >>= \r -> R.resolvePathToModule r path

data DiagnosticSeverity = Error | Warning | Info | Hint
    deriving (Eq, Ord, Show)

data Diagnostic = Diagnostic
    { diagRange :: !TextRange
    , diagSeverity :: !DiagnosticSeverity
    , diagMessage :: !Text
    , diagCode :: !(Maybe Text)
    }
    deriving (Eq, Show)

fromDiagSeverity :: Diag.DiagnosticSeverity -> DiagnosticSeverity
fromDiagSeverity Diag.SeverityError = Error
fromDiagSeverity Diag.SeverityWarning = Warning
fromDiagSeverity Diag.SeverityInfo = Info
fromDiagSeverity Diag.SeverityHint = Hint

fromDiagnostic :: Diag.Diagnostic -> Diagnostic
fromDiagnostic d =
    Diagnostic
        { diagRange = Diag.diagRange d
        , diagSeverity = fromDiagSeverity (Diag.diagSeverity d)
        , diagMessage = Diag.diagMessage d
        , diagCode = Diag.diagCode d
        }

fileDiagnostics :: QueryContext -> FileId -> IO [Diagnostic]
fileDiagnostics ctx fid = do
    query (qcDatabase ctx) "fileDiagnostics" fid $ \_tracker fid' -> do
        mTree <- syntaxTree ctx fid'
        case mTree of
            Nothing -> return []
            Just tree -> do
                let diags = Diag.collectAllDiagnostics tree
                return $ map fromDiagnostic diags

allDiagnostics :: QueryContext -> IO [(FileId, [Diagnostic])]
allDiagnostics ctx = do
    fileInputs <- readTVarIO (qcFileInputs ctx)
    mapM (\fid -> (fid,) <$> fileDiagnostics ctx fid) (HM.keys fileInputs)

data SymbolInfo = SymbolInfo
    { symName :: !Text
    , symKind :: !SymbolKind
    , symRange :: !TextRange
    , symSelectionRange :: !TextRange
    }
    deriving (Eq, Show)

data SymbolKind
    = SymFunction
    | SymType
    | SymConstructor
    | SymTrait
    | SymVariable
    | SymParameter
    deriving (Eq, Show)

fileSymbols :: QueryContext -> FileId -> IO [SymbolInfo]
fileSymbols ctx fid = do
    query (qcDatabase ctx) "fileSymbols" fid $ \_tracker fid' -> do
        mTree <- syntaxTree ctx fid'
        case mTree of
            Nothing -> return []
            Just tree -> return $ extractSymbols tree

extractSymbols :: SyntaxNode -> [SymbolInfo]
extractSymbols = go
  where
    go n =
        let current = extractSymbol n
            childSyms = concatMap go (children n)
        in maybe childSyms (: childSyms) current

    extractSymbol n = case ndKind (unGreenNode (snGreen n)) of
        SK_Node NK_BINDING_DEF -> do
            tok <- firstToken n
            let name = gtText (stGreen tok)
            Just
                SymbolInfo
                    { symName = name
                    , symKind = SymFunction
                    , symRange = TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
                    , symSelectionRange = TextRange (stOffset tok) (fromIntegral $ T.length name)
                    }
        SK_Node NK_DATA_DEF -> do
            tok <- firstToken n
            let name = gtText (stGreen tok)
            Just
                SymbolInfo
                    { symName = name
                    , symKind = SymType
                    , symRange = TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
                    , symSelectionRange = TextRange (stOffset tok) (fromIntegral $ T.length name)
                    }
        SK_Node NK_DATA_CONSTRUCTOR -> do
            tok <- firstToken n
            let name = gtText (stGreen tok)
            Just
                SymbolInfo
                    { symName = name
                    , symKind = SymConstructor
                    , symRange = TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
                    , symSelectionRange = TextRange (stOffset tok) (fromIntegral $ T.length name)
                    }
        SK_Node NK_TRAIT_DEF -> do
            tok <- firstToken n
            let name = gtText (stGreen tok)
            Just
                SymbolInfo
                    { symName = name
                    , symKind = SymTrait
                    , symRange = TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
                    , symSelectionRange = TextRange (stOffset tok) (fromIntegral $ T.length name)
                    }
        _ -> Nothing

resolvedNames :: QueryContext -> FileId -> IO (HM.HashMap Text TextRange)
resolvedNames ctx fid = do
    query (qcDatabase ctx) "resolvedNames" fid $ \_tracker fid' -> do
        mTree <- syntaxTree ctx fid'
        case mTree of
            Nothing -> return HM.empty
            Just tree ->
                let scope = D.buildScope tree
                in return $ HM.fromList [(name, getRange node') | (name, node') <- HM.toList (D.scopeBindings scope)]
  where
    getRange node' = TextRange (snOffset node') (ndTextLen (unGreenNode (snGreen node')))

fileImports :: QueryContext -> FileId -> IO [(Text, [Text])]
fileImports ctx fid = do
    query (qcDatabase ctx) "fileImports" fid $ \_tracker fid' -> do
        mTree <- syntaxTree ctx fid'
        case mTree of
            Nothing -> return []
            Just tree -> return $ extractImports tree

extractImports :: SyntaxNode -> [(Text, [Text])]
extractImports root = concatMap extractImport (children root)
  where
    extractImport n = case ndKind (unGreenNode (snGreen n)) of
        SK_Node NK_IMPORT_DECL ->
            let modName = extractModuleName n
                items = extractImportItems n
            in [(modName, items)]
        _ -> []

    extractModuleName n =
        case childOfKind (SK_Node NK_QUALIFIED_NAME) n of
            Just qname -> text (SyntaxNodeElement qname)
            Nothing -> text (SyntaxNodeElement n)

    extractImportItems n =
        case childOfKind (SK_Node NK_IMPORT_LIST) n of
            Just list -> [gtText (stGreen tok) | tok <- concatMap getTokens (children list)]
            Nothing -> []
    getTokens node' = case firstToken node' of
        Just tok -> [tok]
        Nothing -> []

moduleExports :: QueryContext -> FileId -> IO [Text]
moduleExports ctx fid = do
    symbols <- fileSymbols ctx fid
    return [symName s | s <- symbols]

inferredTypes :: QueryContext -> FileId -> IO (HM.HashMap TextRange Text)
inferredTypes ctx fid = do
    query (qcDatabase ctx) "inferredTypes" fid $ \_tracker fid' -> do
        mTree <- syntaxTree ctx fid'
        case mTree of
            Nothing -> return HM.empty
            Just tree -> return $ extractDeclaredTypes tree

extractDeclaredTypes :: SyntaxNode -> HM.HashMap TextRange Text
extractDeclaredTypes root = HM.fromList $ concatMap extract (children root)
  where
    extract n = case ndKind (unGreenNode (snGreen n)) of
        SK_Node NK_BINDING_DEF ->
            case childOfKind (SK_Node NK_TYPE_SIGNATURE) n of
                Just sig ->
                    let range = TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
                        typeText = text (SyntaxNodeElement sig)
                    in [(range, typeText)]
                Nothing -> []
        _ -> []

symbolType :: QueryContext -> FileId -> Text -> IO (Maybe Text)
symbolType ctx fid symName' = do
    query (qcDatabase ctx) "symbolType" (fid, symName') $ \_tracker (fid', name) -> do
        mTree <- syntaxTree ctx fid'
        case mTree of
            Nothing -> return Nothing
            Just tree -> return $ findSymbolType name tree

findSymbolType :: Text -> SyntaxNode -> Maybe Text
findSymbolType name root = go (children root)
  where
    go [] = Nothing
    go (n : ns) = case ndKind (unGreenNode (snGreen n)) of
        SK_Node NK_BINDING_DEF ->
            case firstToken n of
                Just tok
                    | gtText (stGreen tok) == name ->
                        case childOfKind (SK_Node NK_TYPE_SIGNATURE) n of
                            Just sig -> Just $ text (SyntaxNodeElement sig)
                            Nothing -> Nothing
                _ -> go ns
        _ -> go ns

expressionType :: QueryContext -> FileId -> Word32 -> IO (Maybe Text)
expressionType ctx fid offset = do
    query (qcDatabase ctx) "expressionType" (fid, offset) $ \_tracker (fid', off) -> do
        mTree <- syntaxTree ctx fid'
        case mTree of
            Nothing -> return Nothing
            Just tree ->
                case coveringElement tree off of
                    Nothing -> return Nothing
                    Just elem' -> return $ getExprType elem'
  where
    getExprType (SyntaxNodeElement n) = case ndKind (unGreenNode (snGreen n)) of
        SK_Node NK_EXPR_LITERAL ->
            case firstToken n of
                Just tok -> case gtKind (stGreen tok) of
                    SK_Token TokenNumber -> Just "Int"
                    SK_Token (TokenString _) -> Just "String"
                    SK_Token TokenTrue -> Just "Bool"
                    SK_Token TokenFalse -> Just "Bool"
                    _ -> Nothing
                Nothing -> Nothing
        _ -> Nothing
    getExprType (SyntaxTokenElement tok) = case gtKind (stGreen tok) of
        SK_Token TokenNumber -> Just "Int"
        SK_Token (TokenString _) -> Just "String"
        SK_Token TokenTrue -> Just "Bool"
        SK_Token TokenFalse -> Just "Bool"
        _ -> Nothing

data Location = Location
    { locFile :: !FileId
    , locRange :: !TextRange
    }
    deriving (Eq, Show)

definitionLocation :: QueryContext -> FileId -> Word32 -> IO (Maybe Location)
definitionLocation ctx fid offset = do
    query (qcDatabase ctx) "definitionLocation" (fid, offset) $ \_tracker (fid', off) -> do
        mTree <- syntaxTree ctx fid'
        case mTree of
            Nothing -> return Nothing
            Just tree -> do
                case D.findDefinition (unFileId fid') tree off of
                    Just defResult -> do
                        -- check if it's a cross-module reference
                        case D.defKind defResult of
                            D.DefFunction -> return $ Just $ toLocation defResult
                            D.DefType -> return $ Just $ toLocation defResult
                            _ -> return $ Just $ toLocation defResult
                    Nothing -> do
                        case coveringElement tree off of
                            Just (SyntaxTokenElement tok) -> do
                                let name = gtText (stGreen tok)
                                resolveImportedSymbol ctx fid' tree name
                            _ -> return Nothing
  where
    toLocation dr =
        Location
            { locFile = FileId (D.defFile dr)
            , locRange = D.defRange dr
            }

resolveImportedSymbol :: QueryContext -> FileId -> SyntaxNode -> Text -> IO (Maybe Location)
resolveImportedSymbol ctx _fid tree name = do
    let imports = extractImports tree
    case findImportForSymbol name imports of
        Nothing -> return Nothing
        Just modName -> do
            mPath <- resolveModuleName ctx modName
            case mPath of
                Nothing -> return Nothing
                Just path -> do
                    let targetFid = fileId path
                    mTargetTree <- syntaxTree ctx targetFid
                    case mTargetTree of
                        Nothing -> return Nothing
                        Just targetTree ->
                            case findDefinitionByName name targetTree of
                                Just defNode ->
                                    return
                                        ( Just
                                            Location
                                                { locFile = targetFid
                                                , locRange = TextRange (snOffset defNode) (ndTextLen (unGreenNode (snGreen defNode)))
                                                }
                                        )
                                Nothing -> return Nothing
  where
    findImportForSymbol :: Text -> [(Text, [Text])] -> Maybe Text
    findImportForSymbol sym imps =
        case [m | (m, items) <- imps, null items || sym `elem` items] of
            (m : _) -> Just m
            [] -> Nothing

    findDefinitionByName :: Text -> SyntaxNode -> Maybe SyntaxNode
    findDefinitionByName n root = go (children root)
      where
        go [] = Nothing
        go (node' : ns) = case ndKind (unGreenNode (snGreen node')) of
            SK_Node NK_BINDING_DEF -> checkName node' ns
            SK_Node NK_DATA_DEF -> checkName node' ns
            SK_Node NK_TRAIT_DEF -> checkName node' ns
            _ -> go ns
        checkName node' ns = case firstToken node' of
            Just tok | gtText (stGreen tok) == n -> Just node'
            _ -> go ns

references :: QueryContext -> FileId -> Word32 -> IO [Location]
references ctx fid offset = do
    query (qcDatabase ctx) "references" (fid, offset) $ \_tracker (fid', off) -> do
        mTree <- syntaxTree ctx fid'
        case mTree of
            Nothing -> return []
            Just tree ->
                case coveringElement tree off of
                    Nothing -> return []
                    Just elem' ->
                        let name = case elem' of
                                SyntaxTokenElement tok -> gtText (stGreen tok)
                                SyntaxNodeElement n -> maybe "" (gtText . stGreen) (firstToken n)
                        in findAllReferences ctx fid' name

findAllReferences :: QueryContext -> FileId -> Text -> IO [Location]
findAllReferences ctx _currentFid name = do
    fileInputs <- readTVarIO (qcFileInputs ctx)
    refs <- mapM (findRefsInFile name) (HM.keys fileInputs)
    return $ concat refs
  where
    findRefsInFile n targetFid = do
        mTree <- syntaxTree ctx targetFid
        case mTree of
            Nothing -> return []
            Just tree ->
                return
                    [ Location targetFid (TextRange (stOffset tok) (fromIntegral $ T.length n))
                    | tok <- findIdentifiers n tree
                    ]

    findIdentifiers n = go
      where
        go node' =
            let current = case firstToken node' of
                    Just tok
                        | gtText (stGreen tok) == n
                        , gtKind (stGreen tok) `elem` [SK_Token TokenLowerIdentifier, SK_Token TokenUpperIdentifier] ->
                            [tok]
                    _ -> []
            in current ++ concatMap go (children node')

data HoverInfo = HoverInfo
    { hoverRange :: !TextRange
    , hoverContents :: !Text
    }
    deriving (Eq, Show)

hover :: QueryContext -> FileId -> Word32 -> IO (Maybe HoverInfo)
hover ctx fid offset = do
    query (qcDatabase ctx) "hover" (fid, offset) $ \_tracker (fid', off) -> do
        mTree <- syntaxTree ctx fid'
        case mTree of
            Nothing -> return Nothing
            Just tree ->
                case H.hoverAtPosition tree off of
                    Nothing -> return Nothing
                    Just hi ->
                        return
                            ( Just
                                HoverInfo
                                    { hoverRange = fromMaybe (TextRange off 0) (H.hiRange hi)
                                    , hoverContents = H.formatHoverMarkdown hi
                                    }
                            )

data CompletionItem = CompletionItem
    { ciLabel :: !Text
    , ciKind :: !CompletionKind
    , ciDetail :: !(Maybe Text)
    , ciInsertText :: !(Maybe Text)
    }
    deriving (Eq, Show)

data CompletionKind
    = CKFunction
    | CKType
    | CKConstructor
    | CKVariable
    | CKKeyword
    deriving (Eq, Show)

fromCompletionKind :: C.CompletionKind -> CompletionKind
fromCompletionKind C.CKFunction = CKFunction
fromCompletionKind C.CKVariable = CKVariable
fromCompletionKind C.CKParameter = CKVariable
fromCompletionKind C.CKType = CKType
fromCompletionKind C.CKConstructor = CKConstructor
fromCompletionKind C.CKTrait = CKType
fromCompletionKind C.CKKeyword = CKKeyword
fromCompletionKind C.CKModule = CKVariable
fromCompletionKind C.CKField = CKVariable
fromCompletionKind C.CKOperator = CKFunction

fromCompletionItem :: C.CompletionItem -> CompletionItem
fromCompletionItem ci =
    CompletionItem
        { ciLabel = C.ciLabel ci
        , ciKind = fromCompletionKind (C.ciKind ci)
        , ciDetail = C.ciDetail ci
        , ciInsertText = C.ciInsertText ci
        }

completions :: QueryContext -> FileId -> Word32 -> IO [CompletionItem]
completions ctx fid offset = do
    query (qcDatabase ctx) "completions" (fid, offset) $ \_tracker (fid', off) -> do
        mTree <- syntaxTree ctx fid'
        mText <- sourceText ctx fid'
        case (mTree, mText) of
            (Just tree, Just txt) -> do
                let prefix = extractPrefix txt off
                let items = C.completionsAt tree off prefix
                return $ map fromCompletionItem items
            _ -> return []
  where
    extractPrefix txt off =
        let before = T.take (fromIntegral off) txt
            word = T.takeWhileEnd isIdentChar before
        in word
    isIdentChar c = c `elem` ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ ['_']
