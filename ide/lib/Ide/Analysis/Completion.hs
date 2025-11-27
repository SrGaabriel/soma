module Ide.Analysis.Completion (
    CompletionItem (..),
    CompletionKind (..),
    CompletionContext (..),
    completionsAt,
    completeIdentifier,
    completeType,
    completeKeyword,
    filterCompletions,
    sortCompletions,
    fuzzyMatch,
) where

import Data.Char (toLower)
import Data.HashMap.Strict qualified as HM
import Data.List (sortBy)
import Data.Maybe (mapMaybe)
import Data.Ord (Down (..))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word32)
import Ide.Analysis.Definition (Scope (..), buildScopeAt)
import Syntax.CST.GreenTree (gtText, ndKind, unGreenNode)
import Syntax.CST.RedTree
import Syntax.CST.SyntaxKind
import Utils.Lists (hardHead)

data CompletionItem = CompletionItem
    { ciLabel :: !Text
    , ciKind :: !CompletionKind
    , ciDetail :: !(Maybe Text)
    , ciDocumentation :: !(Maybe Text)
    , ciInsertText :: !(Maybe Text)
    , ciFilterText :: !(Maybe Text)
    , ciSortText :: !(Maybe Text)
    , ciScore :: !Int
    }
    deriving (Eq, Show)

data CompletionKind
    = CKFunction
    | CKVariable
    | CKParameter
    | CKType
    | CKConstructor
    | CKTrait
    | CKKeyword
    | CKModule
    | CKField
    | CKOperator
    deriving (Eq, Show, Ord)

data CompletionContext = CompletionContext
    { ccTriggerKind :: !TriggerKind
    , ccTriggerChar :: !(Maybe Char)
    , ccPrefix :: !Text
    , ccIsTypePosition :: !Bool
    , ccIsPatternPosition :: !Bool
    }
    deriving (Eq, Show)

data TriggerKind
    = TriggerInvoked
    | TriggerCharacter
    | TriggerIncomplete
    deriving (Eq, Show)

completionsAt :: SyntaxNode -> Word32 -> Text -> [CompletionItem]
completionsAt root offset prefix =
    let ctx = analyzeContext root offset prefix
        scope = buildScopeAt root offset

        scopeCompletions = completeFromScope scope prefix
        keywordCompletions = if ccIsTypePosition ctx then [] else completeKeyword prefix
        typeCompletions = if ccIsTypePosition ctx then completeBuiltinTypes prefix else []
    in sortCompletions $ scopeCompletions ++ keywordCompletions ++ typeCompletions

analyzeContext :: SyntaxNode -> Word32 -> Text -> CompletionContext
analyzeContext root offset prefix =
    let element = coveringElement root offset
        isType = maybe False isInTypePosition element
        isPattern = maybe False isInPatternPosition element
    in CompletionContext
        { ccTriggerKind = TriggerInvoked
        , ccTriggerChar = Nothing
        , ccPrefix = prefix
        , ccIsTypePosition = isType
        , ccIsPatternPosition = isPattern
        }
  where
    isInTypePosition (SyntaxNodeElement n) =
        any isTypeNode (n : ancestors n)
    isInTypePosition (SyntaxTokenElement t) =
        any isTypeNode (stParent t : ancestors (stParent t))

    isTypeNode n =
        ndKind (unGreenNode (snGreen n))
            `elem` [SK_Node NK_TYPE, SK_Node NK_TYPE_SIGNATURE, SK_Node NK_CONSTRAINT]

    isInPatternPosition (SyntaxNodeElement n) =
        any isPatternNode (n : ancestors n)
    isInPatternPosition (SyntaxTokenElement t) =
        any isPatternNode (stParent t : ancestors (stParent t))

    isPatternNode n =
        ndKind (unGreenNode (snGreen n))
            `elem` [SK_Node NK_PATTERN, SK_Node NK_MATCH_ARM]

completeFromScope :: Scope -> Text -> [CompletionItem]
completeFromScope scope prefix =
    let bindings = HM.toList (scopeBindings scope)
        parentCompletions = maybe [] (`completeFromScope` prefix) (scopeParent scope)
        localCompletions = mapMaybe (bindingToCompletion prefix) bindings
    in localCompletions ++ parentCompletions
  where
    bindingToCompletion pfx (name, node)
        | fuzzyMatch pfx name =
            Just
                $ CompletionItem
                    { ciLabel = name
                    , ciKind = nodeToCompletionKind node
                    , ciDetail = extractTypeSignature node
                    , ciDocumentation = Nothing
                    , ciInsertText = Nothing
                    , ciFilterText = Just name
                    , ciSortText = Nothing
                    , ciScore = fuzzyScore pfx name
                    }
        | otherwise = Nothing

    extractTypeSignature n = case childOfKind (SK_Node NK_TYPE_SIGNATURE) n of
        Just sigNode -> Just $ text (SyntaxNodeElement sigNode)
        Nothing -> Nothing

    nodeToCompletionKind n = case ndKind (unGreenNode (snGreen n)) of
        SK_Node NK_BINDING_DEF -> CKFunction
        SK_Node NK_DATA_DEF -> CKType
        SK_Node NK_DATA_CONSTRUCTOR -> CKConstructor
        SK_Node NK_TRAIT_DEF -> CKTrait
        SK_Node NK_PARAM -> CKParameter
        _ -> CKVariable

completeIdentifier :: Scope -> Text -> [CompletionItem]
completeIdentifier = completeFromScope

completeType :: SyntaxNode -> Text -> [CompletionItem]
completeType root prefix =
    let typeNodes = findAllTypeDefinitions root
        builtins = completeBuiltinTypes prefix
    in builtins ++ mapMaybe (typeToCompletion prefix) typeNodes
  where
    typeToCompletion pfx node = do
        tok <- firstToken node
        let name = gtText (stGreen tok)
        if fuzzyMatch pfx name
            then
                Just
                    $ CompletionItem
                        { ciLabel = name
                        , ciKind = CKType
                        , ciDetail = Just "type"
                        , ciDocumentation = Nothing
                        , ciInsertText = Nothing
                        , ciFilterText = Just name
                        , ciSortText = Nothing
                        , ciScore = fuzzyScore pfx name
                        }
            else Nothing

findAllTypeDefinitions :: SyntaxNode -> [SyntaxNode]
findAllTypeDefinitions n =
    let current = ([n | isTypeDef n])
    in current ++ concatMap findAllTypeDefinitions (children n)
  where
    isTypeDef node =
        ndKind (unGreenNode (snGreen node))
            `elem` [SK_Node NK_DATA_DEF, SK_Node NK_TRAIT_DEF, SK_Node NK_INTRINSIC_DATA]

completeBuiltinTypes :: Text -> [CompletionItem]
completeBuiltinTypes prefix =
    filter
        (fuzzyMatch prefix . ciLabel)
        [ mkTypeItem "Int" "Built-in integer type"
        , mkTypeItem "String" "Built-in string type"
        , mkTypeItem "Bool" "Built-in boolean type"
        , mkTypeItem "Float" "Built-in floating-point type"
        , mkTypeItem "Byte" "Built-in byte type"
        , mkTypeItem "Array" "Built-in array type (Array a)"
        , mkTypeItem "IO" "IO monad for effectful computations"
        , mkTypeItem "Ref" "Mutable reference type"
        ]
  where
    mkTypeItem name doc =
        CompletionItem
            { ciLabel = name
            , ciKind = CKType
            , ciDetail = Just "built-in"
            , ciDocumentation = Just doc
            , ciInsertText = Nothing
            , ciFilterText = Just name
            , ciSortText = Just ("0" <> name) -- Sort builtins first
            , ciScore = 100
            }

completeKeyword :: Text -> [CompletionItem]
completeKeyword prefix =
    filter
        (fuzzyMatch prefix . ciLabel)
        [ mkKeyword "def" "Define a function or value"
        , mkKeyword "data" "Define an algebraic data type"
        , mkKeyword "trait" "Define a type class"
        , mkKeyword "instance" "Define a type class instance"
        , mkKeyword "where" "Begin definition block"
        , mkKeyword "use" "Import from a module"
        , mkKeyword "if" "Conditional expression"
        , mkKeyword "then" "Then branch of conditional"
        , mkKeyword "else" "Else branch of conditional"
        , mkKeyword "let" "Local binding"
        , mkKeyword "in" "Body of let expression"
        , mkKeyword "compose" "Monadic composition block"
        , mkKeyword "intrinsic" "Declare intrinsic binding"
        ]
  where
    mkKeyword kw doc =
        CompletionItem
            { ciLabel = kw
            , ciKind = CKKeyword
            , ciDetail = Just "keyword"
            , ciDocumentation = Just doc
            , ciInsertText = Nothing
            , ciFilterText = Just kw
            , ciSortText = Just ("2" <> kw) -- Sort keywords after types
            , ciScore = 50
            }

filterCompletions :: Text -> [CompletionItem] -> [CompletionItem]
filterCompletions prefix = filter (fuzzyMatch prefix . ciLabel)

sortCompletions :: [CompletionItem] -> [CompletionItem]
sortCompletions = sortBy compareItems
  where
    compareItems a b =
        compare (Down $ ciScore a) (Down $ ciScore b)
            <> compare (ciKind a) (ciKind b)
            <> compare (ciLabel a) (ciLabel b)

fuzzyMatch :: Text -> Text -> Bool
fuzzyMatch query candidate
    | T.null query = True
    | otherwise = go (T.unpack $ T.toLower query) (T.unpack $ T.toLower candidate)
  where
    go [] _ = True
    go _ [] = False
    go (q : qs) (c : cs)
        | q == c = go qs cs
        | otherwise = go (q : qs) cs

fuzzyScore :: Text -> Text -> Int
fuzzyScore query candidate
    | T.null query = 100
    | query == candidate = 1000
    | T.toLower query == T.toLower candidate = 900
    | T.isPrefixOf query candidate = 800
    | T.isPrefixOf (T.toLower query) (T.toLower candidate) = 700
    | fuzzyMatch query candidate = scoreMatch (T.unpack query) (T.unpack candidate) 0
    | otherwise = 0
  where
    scoreMatch [] _ score = score
    scoreMatch _ [] score = score
    scoreMatch (q : qs) (c : cs) score
        | toLower q == toLower c =
            let bonus = if q == c then 10 else 5
                consecutive
                    | null qs || null cs = 0
                    | hardHead qs == hardHead cs = 20
                    | otherwise = 0
            in scoreMatch qs cs (score + bonus + consecutive)
        | otherwise = scoreMatch (q : qs) cs (score - 1)
