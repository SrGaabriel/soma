{-# LANGUAGE NamedFieldPuns #-}

module Metal.Gen.Metadata where

import Data.Map (Map)
import qualified Data.Map as Map
import Metal.Metadata
import Syntax.Tree

extractConstructorMetadata :: Expr -> Map String MetallicConstructorMetadata
extractConstructorMetadata (ExprRoot decls) =
    Map.fromList $ concat [extractFromDataType dt | dt@(ExprDataTypeDef{}) <- decls]
  where
    extractFromDataType (ExprDataTypeDef{dataName, dataConstructors}) =
        [ (ctorName, MetallicConstructorMetadata dataName tag fieldTypes)
        | ( tag
            , ExprDataConstructor
                { structConstructorName = ctorName
                , structConstructorArgs = fields
                }
            ) <-
            zip [0 ..] dataConstructors
        , let fieldTypes = map snd fields
        ]
    extractFromDataType _ = []
extractConstructorMetadata _ = Map.empty
