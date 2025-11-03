{-# LANGUAGE NamedFieldPuns #-}

module Metal.Gen.DataTypes (
    compileDataTypeDef,
    compileDataTypeDefsFromRoot,
) where

import Metal.Gen.Core (MetalGen, addType)
import Metal.Module (
    MetallicConstructor (..),
    MetallicTypeDef (..),
 )
import Syntax.Tree (Expr (..))

compileDataTypeDef :: Expr -> MetalGen ()
compileDataTypeDef (ExprDataTypeDef{dataName, dataConstructors}) = do
    let ctors = buildConstructors dataConstructors
        tyDef =
            MAlgebraicType
                { mtName = dataName
                , mtConstructors = ctors
                }
    addType dataName tyDef
compileDataTypeDef _ = pure ()

compileDataTypeDefsFromRoot :: Expr -> MetalGen ()
compileDataTypeDefsFromRoot (ExprRoot decls) =
    mapM_ compileDataTypeDef [d | d@(ExprDataTypeDef{}) <- decls]
compileDataTypeDefsFromRoot _ = pure ()

buildConstructors :: [Expr] -> [MetallicConstructor]
buildConstructors ctors =
    [ buildOne tag c
    | (tag, c) <- zip [0 ..] ctors
    , isDataConstructor c
    ]
  where
    isDataConstructor :: Expr -> Bool
    isDataConstructor ExprDataConstructor{} = True
    isDataConstructor _ = False

    buildOne :: Int -> Expr -> MetallicConstructor
    buildOne tag (ExprDataConstructor{structConstructorName, structConstructorArgs}) =
        MetallicConstructor
            { mcName = structConstructorName
            , mcTag = tag
            , mcFields = map snd structConstructorArgs
            }
    buildOne _ other =
        error $ "Unexpected non-constructor in dataConstructors: " ++ show other
