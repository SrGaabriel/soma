module Llvm.Gen.Monomorphize (monomorphizeAndCompile) where

import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Llvm.Gen.Context
import Llvm.Gen.Core (IrGen, IrGenState (..))
import Llvm.Gen.Functions (compileFunction)
import Llvm.Gen.Mangling (mangleMonomorphizedName)
import Llvm.Gen.Metadata (PolymorphicFunctionMetadata (..))
import Llvm.Gen.Types (toAllocationLlvmType)
import Syntax.Tree (Expr (..))
import Typing.Types (Kind (..), QualifiedType (Forall), TyVar (..), Type (..))

monomorphizeAndCompile :: String -> [Type] -> (Expr -> IrGen GenValue) -> IrGen String
monomorphizeAndCompile funcName argTypes compileValueFunc = do
    st <- get
    let llvmArgTypes = map toAllocationLlvmType argTypes
    let mangledName = mangleMonomorphizedName funcName llvmArgTypes

    if Set.member mangledName (monomorphizedFunctions st)
        then return mangledName
        else do
            case Map.lookup funcName (polymorphicFunctions st) of
                Nothing -> error $ "Polymorphic function not found: " ++ funcName
                Just (PolymorphicFunction _ (Forall typeVars _ originalType) body) -> do
                    let typeVarNames = map (\(TypeVar name _) -> name) typeVars
                    let substitution = Map.fromList $ zip typeVarNames argTypes
                    let monomorphicType = substituteType substitution originalType

                    modify $ \s -> s{monomorphizedFunctions = Set.insert mangledName (monomorphizedFunctions s)}

                    compileFunction mangledName monomorphicType body compileValueFunc

                    return mangledName

substituteType :: Map.Map String Type -> Type -> Type
substituteType subst (TVar (TypeVar name _)) =
    case Map.lookup name subst of
        Just t -> t
        Nothing -> TVar (TypeVar name KindStar)
substituteType subst (TApp t1 t2) =
    TApp (substituteType subst t1) (substituteType subst t2)
substituteType subst (TArrow t1 t2) =
    TArrow (substituteType subst t1) (substituteType subst t2)
substituteType _ t = t
