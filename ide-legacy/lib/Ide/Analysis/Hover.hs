module Ide.Analysis.Hover (
    HoverInfo (..),
    HoverContents (..),
    hoverAtPosition,
    hoverForNode,
    hoverForToken,
    formatHoverMarkdown,
    formatType,
) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word32)
import Ide.Analysis.Definition qualified as D
import Syntax.CST.GreenTree (TextRange (..), gtKind, gtText, ndKind, ndTextLen, unGreenNode)
import Syntax.CST.RedTree
import Syntax.CST.SyntaxKind

data HoverContents
    = HoverText !Text
    | HoverMarkdown !Text
    | HoverCode !Text !Text
    deriving (Eq, Show)

data HoverInfo = HoverInfo
    { hiContents :: ![HoverContents]
    , hiRange :: !(Maybe TextRange)
    }
    deriving (Eq, Show)

hoverAtPosition :: SyntaxNode -> Word32 -> Maybe HoverInfo
hoverAtPosition root offset = do
    element <- coveringElement root offset
    case element of
        SyntaxTokenElement tok -> hoverForToken tok
        SyntaxNodeElement node -> hoverForNodeWithRoot root node

hoverForNodeWithRoot :: SyntaxNode -> SyntaxNode -> Maybe HoverInfo
hoverForNodeWithRoot root n = case ndKind (unGreenNode (snGreen n)) of
    SK_Node NK_BINDING_DEF -> hoverForBinding n
    SK_Node NK_DATA_DEF -> hoverForDataDef n
    SK_Node NK_DATA_CONSTRUCTOR -> hoverForConstructor n
    SK_Node NK_TRAIT_DEF -> hoverForTrait n
    SK_Node NK_INSTANCE_DEF -> hoverForInstance n
    SK_Node NK_EXPR_VAR -> hoverForVarRef root n
    SK_Node NK_TYPE -> hoverForTypeExpr n
    _ -> Nothing

hoverForNode :: SyntaxNode -> Maybe HoverInfo
hoverForNode n = case ndKind (unGreenNode (snGreen n)) of
    SK_Node NK_BINDING_DEF -> hoverForBinding n
    SK_Node NK_DATA_DEF -> hoverForDataDef n
    SK_Node NK_DATA_CONSTRUCTOR -> hoverForConstructor n
    SK_Node NK_TRAIT_DEF -> hoverForTrait n
    SK_Node NK_INSTANCE_DEF -> hoverForInstance n
    SK_Node NK_TYPE -> hoverForTypeExpr n
    _ -> Nothing

hoverForToken :: SyntaxToken -> Maybe HoverInfo
hoverForToken tok = case gtKind (stGreen tok) of
    SK_Token TokenLowerIdentifier ->
        Just
            $ HoverInfo
                { hiContents = [HoverText $ "identifier: " <> gtText (stGreen tok)]
                , hiRange = Just $ TextRange (stOffset tok) (fromIntegral $ T.length $ gtText (stGreen tok))
                }
    SK_Token TokenUpperIdentifier ->
        Just
            $ HoverInfo
                { hiContents = [HoverText $ "type/constructor: " <> gtText (stGreen tok)]
                , hiRange = Just $ TextRange (stOffset tok) (fromIntegral $ T.length $ gtText (stGreen tok))
                }
    SK_Token TokenNumber ->
        Just
            $ HoverInfo
                { hiContents = [HoverCode "Int" "soma"]
                , hiRange = Just $ TextRange (stOffset tok) (fromIntegral $ T.length $ gtText (stGreen tok))
                }
    SK_Token (TokenString _) ->
        Just
            $ HoverInfo
                { hiContents = [HoverCode "String" "soma"]
                , hiRange = Just $ TextRange (stOffset tok) (fromIntegral $ T.length $ gtText (stGreen tok))
                }
    _
        | isKeyword (gtKind (stGreen tok)) ->
            Just
                $ HoverInfo
                    { hiContents = [HoverText $ "keyword: " <> gtText (stGreen tok)]
                    , hiRange = Just $ TextRange (stOffset tok) (fromIntegral $ T.length $ gtText (stGreen tok))
                    }
    _ -> Nothing

hoverForBinding :: SyntaxNode -> Maybe HoverInfo
hoverForBinding n = do
    let nameToken = firstToken n
    let typeSig = findTypeSig n

    let nameText = maybe "unknown" (gtText . stGreen) nameToken
    let typeText = maybe "inferred" formatTypeSig typeSig

    Just
        $ HoverInfo
            { hiContents =
                [ HoverMarkdown $ "**" <> nameText <> "**"
                , HoverCode (nameText <> " :: " <> typeText) "soma"
                ]
            , hiRange = Just $ TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
            }
  where
    findTypeSig = childOfKind (SK_Node NK_TYPE_SIGNATURE)
    formatTypeSig sigNode = text (SyntaxNodeElement sigNode)

hoverForDataDef :: SyntaxNode -> Maybe HoverInfo
hoverForDataDef n = do
    let nameToken = firstToken n
    let nameText = maybe "unknown" (gtText . stGreen) nameToken
    let constructors = childrenOfKind (SK_Node NK_DATA_CONSTRUCTOR) n
    let ctorNames = map extractCtorName constructors

    Just
        $ HoverInfo
            { hiContents =
                [ HoverMarkdown $ "**data** " <> nameText
                , HoverText $ "Constructors: " <> T.intercalate ", " ctorNames
                ]
            , hiRange = Just $ TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
            }
  where
    extractCtorName ctor = maybe "?" (gtText . stGreen) (firstToken ctor)

hoverForConstructor :: SyntaxNode -> Maybe HoverInfo
hoverForConstructor n = do
    let nameToken = firstToken n
    let nameText = maybe "unknown" (gtText . stGreen) nameToken

    Just
        $ HoverInfo
            { hiContents = [HoverMarkdown $ "**constructor** " <> nameText]
            , hiRange = Just $ TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
            }

hoverForTrait :: SyntaxNode -> Maybe HoverInfo
hoverForTrait n = do
    let nameToken = firstToken n
    let nameText = maybe "unknown" (gtText . stGreen) nameToken

    Just
        $ HoverInfo
            { hiContents = [HoverMarkdown $ "**trait** " <> nameText]
            , hiRange = Just $ TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
            }

hoverForInstance :: SyntaxNode -> Maybe HoverInfo
hoverForInstance n =
    Just
        $ HoverInfo
            { hiContents = [HoverMarkdown "**instance**"]
            , hiRange = Just $ TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
            }

hoverForVarRef :: SyntaxNode -> SyntaxNode -> Maybe HoverInfo
hoverForVarRef root n = do
    tok <- firstToken n
    let nameText = gtText (stGreen tok)
    let range = TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))

    case D.resolveSymbol root tok of
        D.ResolvedLocal defNode ->
            let typeInfo = extractTypeFromDef defNode
                kindText = defKindToText (ndKind (unGreenNode (snGreen defNode)))
            in Just
                $ HoverInfo
                    { hiContents =
                        [ HoverMarkdown $ "**" <> kindText <> "** " <> nameText
                        , HoverCode (nameText <> " :: " <> typeInfo) "soma"
                        ]
                    , hiRange = Just range
                    }
        D.ResolvedImport modName _symName ->
            Just
                $ HoverInfo
                    { hiContents =
                        [ HoverMarkdown $ "**imported** from " <> modName
                        , HoverCode nameText "soma"
                        ]
                    , hiRange = Just range
                    }
        D.ResolvedModule modName ->
            Just
                $ HoverInfo
                    { hiContents = [HoverMarkdown $ "**module** " <> modName]
                    , hiRange = Just range
                    }
        D.Unresolved ->
            Just
                $ HoverInfo
                    { hiContents = [HoverText $ "unresolved: " <> nameText]
                    , hiRange = Just range
                    }
  where
    extractTypeFromDef :: SyntaxNode -> Text
    extractTypeFromDef defNode =
        case childOfKind (SK_Node NK_TYPE_SIGNATURE) defNode of
            Just sig -> text (SyntaxNodeElement sig)
            Nothing ->
                case childOfKind (SK_Node NK_TYPE) defNode of
                    Just ty -> text (SyntaxNodeElement ty)
                    Nothing -> "inferred"

    defKindToText :: SyntaxKind -> Text
    defKindToText (SK_Node NK_BINDING_DEF) = "function"
    defKindToText (SK_Node NK_PARAM) = "parameter"
    defKindToText (SK_Node NK_PATTERN_VAR) = "variable"
    defKindToText (SK_Node NK_EXPR_LET) = "let binding"
    defKindToText (SK_Node NK_DATA_DEF) = "type"
    defKindToText (SK_Node NK_DATA_CONSTRUCTOR) = "constructor"
    defKindToText (SK_Node NK_TRAIT_DEF) = "trait"
    defKindToText _ = "binding"

hoverForTypeExpr :: SyntaxNode -> Maybe HoverInfo
hoverForTypeExpr n =
    Just
        $ HoverInfo
            { hiContents = [HoverText $ "type: " <> text (SyntaxNodeElement n)]
            , hiRange = Just $ TextRange (snOffset n) (ndTextLen (unGreenNode (snGreen n)))
            }

formatHoverMarkdown :: HoverInfo -> Text
formatHoverMarkdown hi = T.intercalate "\n\n" $ map formatContent (hiContents hi)
  where
    formatContent (HoverText t) = t
    formatContent (HoverMarkdown t) = t
    formatContent (HoverCode code lang) = "```" <> lang <> "\n" <> code <> "\n```"

formatType :: Text -> Text
formatType = id
