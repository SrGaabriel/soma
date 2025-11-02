module Llvm.Gen.DataTypes where

import Control.Monad
import Control.Monad.State
import qualified Data.Map as Map
import Llvm.Dependencies (LlvmDependency (LlvmStructDependency))
import Llvm.Gen.Core
import Llvm.Gen.Mangling (mangleDataTypeName)
import Llvm.Gen.Metadata (ConstructorMetadata (ConstructorMetadata))
import Llvm.Gen.Types (toAllocationLlvmType)
import Llvm.Types
import Syntax.Tree (Expr (..))

compileDataTypeDef :: Expr -> IrGen ()
compileDataTypeDef (ExprDataTypeDef name generics _constraints constructors _span) = do
    when (null generics) $ do
        let structDef = computeUnifiedLayout name constructors
        modify $ \s -> s{irDependencies = structDef : irDependencies s}

    mapM_ (registerConstructorMetadata name) (zip [0 ..] constructors)
compileDataTypeDef _ = error "Expected ExprDataTypeDef"

computeUnifiedLayout :: String -> [Expr] -> LlvmDependency
computeUnifiedLayout typeName constructors =
    let variantSizes = map getADTConstructorSize constructors

        maxSize = if null variantSizes then 0 else maximum variantSizes

        fields = [LlvmI8, LlvmArray maxSize LlvmI8]

        mangledName = mangleDataTypeName typeName
    in LlvmStructDependency mangledName fields

getConstructorDataSize :: Expr -> Int
getConstructorDataSize = getADTConstructorSize

getADTConstructorSize :: Expr -> Int
getADTConstructorSize (ExprDataConstructor _name args _) =
    let fieldLlvmTypes = map (toAllocationLlvmType . snd) args
        (_offsets, totalSize) = computeFieldLayout fieldLlvmTypes
    in totalSize
getADTConstructorSize _ = 0

computeFieldLayout :: [LlvmType] -> ([Int], Int)
computeFieldLayout tys =
    let go offset maxAlign acc [] = (reverse acc, alignUp offset maxAlign)
        go offset maxAlign acc (t : ts) =
            let a = naturalAlignment t
                aligned = alignUp offset a
                sz = sizeForLayout t
                nextOffset = aligned + sz
                nextMax = max maxAlign a
            in go nextOffset nextMax (aligned : acc) ts
    in go 0 1 [] tys

sizeForLayout :: LlvmType -> Int
sizeForLayout (LlvmNamedType _) = 8
sizeForLayout (LlvmFn _ _) = 8
sizeForLayout LlvmVararg = 8
sizeForLayout t = getLlvmTypeSize t

alignUp :: Int -> Int -> Int
alignUp off a =
    let r = off `mod` a
    in if r == 0 then off else off + (a - r)

addConstructorMetadata :: String -> ConstructorMetadata -> IrGen ()
addConstructorMetadata ctorName metadata = do
    modify $ \s ->
        s
            { constructorMap = Map.insert ctorName metadata (constructorMap s)
            }
    return ()

registerConstructorMetadata :: String -> (Int, Expr) -> IrGen ()
registerConstructorMetadata typeName (tag, ExprDataConstructor ctorName args _) = do
    let argTypes = map snd args

    let fieldLlvmTypes = map (toAllocationLlvmType . snd) args
    let (fieldOffsets, _totalSize) = computeFieldLayout fieldLlvmTypes
    let metadata =
            ConstructorMetadata
                typeName
                tag
                argTypes
                fieldLlvmTypes
                fieldOffsets
    addConstructorMetadata ctorName metadata
registerConstructorMetadata _ _ = return ()
