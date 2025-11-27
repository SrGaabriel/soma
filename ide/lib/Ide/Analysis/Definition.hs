module Ide.Analysis.Definition (
    DefinitionResult (..),
    DefinitionKind (..),
    findDefinition,
    findDefinitions,
    resolveSymbol,
    SymbolResolution (..),
    Scope (..),
    ScopeKind (..),
    buildScope,
    buildScopeAt,
    lookupInScope,
) where

import Data.HashMap.Strict qualified as HM
import Data.List (find)
import Data.Maybe (listToMaybe, mapMaybe, maybeToList)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word32)
import Syntax.CST.GreenTree (TextRange (..), gtKind, gtText, ndKind, ndTextLen, unGreenNode)
import Syntax.CST.RedTree hiding (text)
import Syntax.CST.RedTree qualified as R
import Syntax.CST.SyntaxKind

data DefinitionResult = DefinitionResult
    { defFile :: !Text
    , defRange :: !TextRange
    , defSelectionRange :: !TextRange
    , defKind :: !DefinitionKind
    }
    deriving (Eq, Show)

data DefinitionKind
    = DefFunction
    | DefType
    | DefConstructor
    | DefTrait
    | DefTraitMethod
    | DefParameter
    | DefLetBinding
    | DefPatternVar
    deriving (Eq, Show)

data SymbolResolution
    = ResolvedLocal !SyntaxNode -- Defined in local scope
    | ResolvedModule !Text -- Defined in another module (module name)
    | ResolvedImport !Text !Text -- Imported from module (module name, symbol name)
    | Unresolved -- Could not resolve
    deriving (Eq, Show)

data Scope = Scope
    { scopeBindings :: !(HM.HashMap Text SyntaxNode)
    , scopeParent :: !(Maybe Scope)
    , scopeKind :: !ScopeKind
    }
    deriving (Show)

data ScopeKind
    = ModuleScope
    | FunctionScope
    | LetScope
    | PatternScope
    | LambdaScope
    deriving (Eq, Show)

findDefinition :: Text -> SyntaxNode -> Word32 -> Maybe DefinitionResult
findDefinition fid root offset = do
    element <- coveringElement root offset
    case element of
        SyntaxTokenElement tok -> findTokenDefinition fid root tok
        SyntaxNodeElement node -> findNodeDefinition fid root node

findDefinitions :: Text -> SyntaxNode -> Word32 -> [DefinitionResult]
findDefinitions fid root offset =
    maybe [] pure (findDefinition fid root offset)

findTokenDefinition :: Text -> SyntaxNode -> SyntaxToken -> Maybe DefinitionResult
findTokenDefinition fid root tok = case gtKind (stGreen tok) of
    SK_Token TokenLowerIdentifier -> findIdentifierDefinition fid root tok
    SK_Token TokenUpperIdentifier -> findTypeOrConstructorDefinition fid root tok
    _ -> Nothing

findNodeDefinition :: Text -> SyntaxNode -> SyntaxNode -> Maybe DefinitionResult
findNodeDefinition fid root node = case ndKind (unGreenNode (snGreen node)) of
    SK_Node NK_EXPR_VAR -> do
        tok <- firstToken node
        findIdentifierDefinition fid root tok
    SK_Node NK_TYPE_CONSTRUCTOR -> do
        tok <- firstToken node
        findTypeOrConstructorDefinition fid root tok
    _ -> Nothing

findIdentifierDefinition :: Text -> SyntaxNode -> SyntaxToken -> Maybe DefinitionResult
findIdentifierDefinition fid root tok = do
    let name = gtText (stGreen tok)
    let scope = buildScopeAt root (stOffset tok)
    defNode <- lookupInScope name scope
    Just
        $ DefinitionResult
            { defFile = fid
            , defRange = TextRange (snOffset defNode) (ndTextLen (unGreenNode (snGreen defNode)))
            , defSelectionRange = getNameRange defNode
            , defKind = getDefinitionKind defNode
            }

findTypeOrConstructorDefinition :: Text -> SyntaxNode -> SyntaxToken -> Maybe DefinitionResult
findTypeOrConstructorDefinition fid root tok = do
    let name = gtText (stGreen tok)
    defNode <- findTypeDefinition name root
    Just
        $ DefinitionResult
            { defFile = fid
            , defRange = TextRange (snOffset defNode) (ndTextLen (unGreenNode (snGreen defNode)))
            , defSelectionRange = getNameRange defNode
            , defKind = getDefinitionKind defNode
            }

buildScopeAt :: SyntaxNode -> Word32 -> Scope
buildScopeAt root offset =
    let moduleScope = buildModuleScope root
    in refineScope moduleScope root offset

buildModuleScope :: SyntaxNode -> Scope
buildModuleScope root =
    Scope
        { scopeBindings = HM.fromList $ mapMaybe extractBinding (children root)
        , scopeParent = Nothing
        , scopeKind = ModuleScope
        }
  where
    extractBinding node = case ndKind (unGreenNode (snGreen node)) of
        SK_Node NK_BINDING_DEF -> do
            tok <- firstToken node
            Just (gtText (stGreen tok), node)
        SK_Node NK_DATA_DEF -> do
            tok <- firstToken node
            Just (gtText (stGreen tok), node)
        SK_Node NK_TRAIT_DEF -> do
            tok <- firstToken node
            Just (gtText (stGreen tok), node)
        _ -> Nothing

refineScope :: Scope -> SyntaxNode -> Word32 -> Scope
refineScope parentScope node offset =
    case findContainingChild node offset of
        Nothing -> parentScope
        Just child ->
            let childScope = extendScope parentScope child
            in refineScope childScope child offset

findContainingChild :: SyntaxNode -> Word32 -> Maybe SyntaxNode
findContainingChild node offset =
    find (`containsOffset'` offset) (children node)
  where
    containsOffset' n o =
        let start = snOffset n
            len = ndTextLen (unGreenNode (snGreen n))
        in o >= start && o < start + len

extendScope :: Scope -> SyntaxNode -> Scope
extendScope parentScope node = case ndKind (unGreenNode (snGreen node)) of
    SK_Node NK_BINDING_DEF ->
        let params = extractParams node
        in Scope
            { scopeBindings = HM.fromList params
            , scopeParent = Just parentScope
            , scopeKind = FunctionScope
            }
    SK_Node NK_EXPR_LET ->
        let bindings = extractLetBindings node
        in Scope
            { scopeBindings = HM.fromList bindings
            , scopeParent = Just parentScope
            , scopeKind = LetScope
            }
    SK_Node NK_EXPR_LAMBDA ->
        let params = extractLambdaParams node
        in Scope
            { scopeBindings = HM.fromList params
            , scopeParent = Just parentScope
            , scopeKind = LambdaScope
            }
    SK_Node NK_MATCH_ARM ->
        let patternVars = extractPatternVars node
        in Scope
            { scopeBindings = HM.fromList patternVars
            , scopeParent = Just parentScope
            , scopeKind = PatternScope
            }
    _ -> parentScope

extractParams :: SyntaxNode -> [(Text, SyntaxNode)]
extractParams node =
    case childOfKind (SK_Node NK_PARAM_LIST) node of
        Nothing -> []
        Just paramList -> mapMaybe extractParam (children paramList)
  where
    extractParam param = do
        tok <- firstToken param
        Just (gtText (stGreen tok), param)

extractLetBindings :: SyntaxNode -> [(Text, SyntaxNode)]
extractLetBindings node =
    concatMap extractFromChild (children node)
  where
    extractFromChild child = case ndKind (unGreenNode (snGreen child)) of
        SK_Node NK_PATTERN -> extractPatternBindings child
        SK_Node NK_PATTERN_VAR -> extractPatternBindings child
        SK_Node NK_BINDING_DEF ->
            case firstToken child of
                Just tok -> [(gtText (stGreen tok), child)]
                Nothing -> []
        _ -> []

extractLambdaParams :: SyntaxNode -> [(Text, SyntaxNode)]
extractLambdaParams node =
    concatMap extractFromChild (children node)
  where
    extractFromChild child = case ndKind (unGreenNode (snGreen child)) of
        SK_Node NK_PARAM_LIST -> mapMaybe extractParam (children child)
        SK_Node NK_PARAM -> maybeToList (extractParam child)
        SK_Node NK_PATTERN -> extractPatternBindings child
        SK_Node NK_PATTERN_VAR -> extractPatternBindings child
        _ -> []
    extractParam param = do
        tok <- firstToken param
        Just (gtText (stGreen tok), param)

extractPatternVars :: SyntaxNode -> [(Text, SyntaxNode)]
extractPatternVars node =
    concatMap extractFromChild (children node)
  where
    extractFromChild child = case ndKind (unGreenNode (snGreen child)) of
        SK_Node NK_PATTERN -> extractPatternBindings child
        SK_Node NK_PATTERN_VAR -> extractPatternBindings child
        SK_Node NK_PATTERN_CONSTRUCTOR -> extractPatternBindings child
        SK_Node NK_PATTERN_AS -> extractPatternBindings child
        SK_Node NK_PATTERN_TUPLE -> extractPatternBindings child
        SK_Node NK_PATTERN_LIST -> extractPatternBindings child
        _ -> []

extractPatternBindings :: SyntaxNode -> [(Text, SyntaxNode)]
extractPatternBindings node = case ndKind (unGreenNode (snGreen node)) of
    SK_Node NK_PATTERN_VAR ->
        case firstToken node of
            Just tok ->
                let name = gtText (stGreen tok)
                in ([(name, node) | name /= "_"])
            Nothing -> []
    SK_Node NK_PATTERN_CONSTRUCTOR ->
        concatMap extractPatternBindings (children node)
    SK_Node NK_PATTERN_AS ->
        let maybeAlias = do
                tok <- firstToken node
                let name = gtText (stGreen tok)
                if name == "_" then Nothing else Just (name, node)
            nested = concatMap extractPatternBindings (children node)
        in maybe nested (: nested) maybeAlias
    SK_Node NK_PATTERN_TUPLE ->
        concatMap extractPatternBindings (children node)
    SK_Node NK_PATTERN_LIST ->
        concatMap extractPatternBindings (children node)
    SK_Node NK_PATTERN ->
        concatMap extractPatternBindings (children node)
    SK_Token TokenLowerIdentifier ->
        let name = case firstToken node of
                Just tok -> gtText (stGreen tok)
                Nothing -> ""
        in ([(name, node) | not (T.null name || name == "_")])
    _ ->
        concatMap extractPatternBindings (children node)

lookupInScope :: Text -> Scope -> Maybe SyntaxNode
lookupInScope name scope =
    case HM.lookup name (scopeBindings scope) of
        Just node -> Just node
        Nothing -> scopeParent scope >>= lookupInScope name

buildScope :: SyntaxNode -> Scope
buildScope = buildModuleScope

resolveSymbol :: SyntaxNode -> SyntaxToken -> SymbolResolution
resolveSymbol root tok =
    let name = gtText (stGreen tok)
        scope = buildScopeAt root (stOffset tok)
    in case lookupInScope name scope of
        Just node -> ResolvedLocal node
        Nothing ->
            case findImportForSymbol name root of
                Just modName -> ResolvedImport modName name
                Nothing -> Unresolved
  where
    findImportForSymbol :: Text -> SyntaxNode -> Maybe Text
    findImportForSymbol symName rootNode =
        listToMaybe $ mapMaybe (checkImportDecl symName) (children rootNode)

    checkImportDecl :: Text -> SyntaxNode -> Maybe Text
    checkImportDecl symName importNode = case ndKind (unGreenNode (snGreen importNode)) of
        SK_Node NK_IMPORT_DECL -> do
            modName <- getImportModuleName importNode
            if importsSymbol symName importNode
                then Just modName
                else Nothing
        _ -> Nothing

    getImportModuleName :: SyntaxNode -> Maybe Text
    getImportModuleName importNode =
        case childOfKind (SK_Node NK_QUALIFIED_NAME) importNode of
            Just qname -> Just $ R.text (SyntaxNodeElement qname)
            Nothing ->
                case filter isModuleNameToken (childrenWithTokens importNode) of
                    [] -> Nothing
                    toks -> Just $ T.intercalate "/" $ map extractText toks
      where
        isModuleNameToken (SyntaxTokenElement t) =
            gtKind (stGreen t) == SK_Token TokenLowerIdentifier
                || gtKind (stGreen t) == SK_Token TokenUpperIdentifier
        isModuleNameToken _ = False
        extractText (SyntaxTokenElement t) = gtText (stGreen t)
        extractText (SyntaxNodeElement n) = R.text (SyntaxNodeElement n)

    importsSymbol :: Text -> SyntaxNode -> Bool
    importsSymbol symName importNode =
        case childOfKind (SK_Node NK_IMPORT_LIST) importNode of
            Nothing -> True -- No import list means wildcard import
            Just importList ->
                any (matchesSymbol symName) (children importList)

    matchesSymbol :: Text -> SyntaxNode -> Bool
    matchesSymbol symName item = case ndKind (unGreenNode (snGreen item)) of
        SK_Node NK_IMPORT_ITEM ->
            case firstToken item of
                Just tok' -> gtText (stGreen tok') == symName
                Nothing -> False
        _ -> False

findTypeDefinition :: Text -> SyntaxNode -> Maybe SyntaxNode
findTypeDefinition name root =
    find (matchesName name) (findTypeNodes root)
  where
    findTypeNodes n =
        let current = ([n | isTypeDefKind (ndKind (unGreenNode (snGreen n)))])
        in current ++ concatMap findTypeNodes (children n)

    isTypeDefKind (SK_Node NK_DATA_DEF) = True
    isTypeDefKind (SK_Node NK_TRAIT_DEF) = True
    isTypeDefKind (SK_Node NK_INTRINSIC_DATA) = True
    isTypeDefKind _ = False

    matchesName nm node =
        case firstToken node of
            Just tok -> gtText (stGreen tok) == nm
            Nothing -> False

getNameRange :: SyntaxNode -> TextRange
getNameRange node =
    case firstToken node of
        Just tok -> TextRange (stOffset tok) (fromIntegral $ T.length $ gtText (stGreen tok))
        Nothing -> TextRange (snOffset node) (ndTextLen (unGreenNode (snGreen node)))

getDefinitionKind :: SyntaxNode -> DefinitionKind
getDefinitionKind node = case ndKind (unGreenNode (snGreen node)) of
    SK_Node NK_BINDING_DEF -> DefFunction
    SK_Node NK_DATA_DEF -> DefType
    SK_Node NK_DATA_CONSTRUCTOR -> DefConstructor
    SK_Node NK_TRAIT_DEF -> DefTrait
    SK_Node NK_TRAIT_METHOD -> DefTraitMethod
    SK_Node NK_PARAM -> DefParameter
    SK_Node NK_EXPR_LET -> DefLetBinding
    SK_Node NK_PATTERN_VAR -> DefPatternVar
    _ -> DefFunction
