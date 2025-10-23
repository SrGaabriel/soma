module Llvm.Gen.DataTypes where

import Control.Monad
import Control.Monad.State
import qualified Data.Map as Map
import Llvm.Gen.Core
import Llvm.Gen.Metadata (ConstructorMetadata (ConstructorMetadata))
import Llvm.Gen.Types (toAllocationLlvmType)
import Llvm.Modules (LlvmStruct (LlvmStruct))
import Llvm.Types
import Syntax.Tree (Expr (..))
import Llvm.Gen.Mangling (mangleDataTypeName)

compileDataTypeDef :: Expr -> IrGen ()
compileDataTypeDef (ExprDataTypeDef name generics _constraints constructors _span) = do
    when (null generics) $ do
        let structDef = computeUnifiedLayout name constructors
        modify $ \s -> s{irStructs = structDef : irStructs s}

    mapM_ (registerConstructorMetadata name) (zip [0 ..] constructors)
compileDataTypeDef _ = error "Expected ExprDataTypeDef"

computeUnifiedLayout :: String -> [Expr] -> LlvmStruct
computeUnifiedLayout typeName constructors =
    let variantSizes = map getConstructorDataSize constructors
        maxSize = if null variantSizes then 0 else maximum variantSizes
        fields = [LlvmI8, LlvmArray maxSize LlvmI8]
        mangledName = mangleDataTypeName typeName
    in LlvmStruct mangledName fields

getConstructorDataSize :: Expr -> Int
getConstructorDataSize (ExprDataConstructor _name args _) = do
    sum (map (getLlvmTypeSize . toAllocationLlvmType . snd) args)
getConstructorDataSize _ = 0

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
    let metadata = ConstructorMetadata typeName tag argTypes

    addConstructorMetadata ctorName metadata
registerConstructorMetadata _ _ = return ()
