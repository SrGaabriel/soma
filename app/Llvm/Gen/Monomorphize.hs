module Llvm.Gen.Monomorphize (monomorphizeAndCompile) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as Map
import qualified Data.Set as Set
import Llvm.Gen.Core (IrGen, IrGenEnv (..), IrGenState (..), MemoryScope (..), freshReg, freshScope)
import Llvm.Gen.Types (toAllocationLlvmType, typeToMonomorphicName)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (..))
import Llvm.Modules (LlvmFunction (..))
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..), getValueType)
import Syntax.Tree (Expr (..))
import Typing.Currying (uncurryFunction)
import Typing.Types (Kind (..), QualifiedType (Forall), TyVar (..), Type (..))
import Llvm.Gen.Metadata (PolymorphicFunctionMetadata(..))

monomorphizeAndCompile :: String -> [Type] -> (Expr -> IrGen LlvmValue) -> IrGen String
monomorphizeAndCompile funcName concreteTypes compileValueFunc = do
    st <- get
    let mangledName = funcName ++ concatMap (("_" ++) . typeToMonomorphicName) concreteTypes

    if Set.member mangledName (monomorphizedFunctions st)
        then return mangledName
        else do
            case Map.lookup funcName (polymorphicFunctions st) of
                Nothing -> error $ "Polymorphic function not found: " ++ funcName
                Just (PolymorphicFunction _ (Forall typeVars _ originalType) body) -> do
                    let typeVarNames = map (\(TypeVar name _) -> name) typeVars
                    let substitution = Map.fromList $ zip typeVarNames concreteTypes
                    let monomorphicType = substituteType substitution originalType

                    modify $ \s -> s{monomorphizedFunctions = Set.insert mangledName (monomorphizedFunctions s)}

                    env <- ask
                    let (fnArgs, fnRetType) = uncurryFunction monomorphicType
                    fnArgRegs <- mapM (freshReg . toAllocationLlvmType) fnArgs
                    newScope <- freshScope mangledName
                    st' <- get
                    let (newEnv, action) = case body of
                            ExprLambda args lambdaBody _ -> do
                                let argBindings = zip args fnArgRegs
                                let updatedScope =
                                        newScope
                                            { blockValues =
                                                Map.fromList (map (\(nam, val) -> (nam, val)) argBindings)
                                                    `Map.union` blockValues newScope
                                            }
                                let updatedEnv = env{currentScope = updatedScope, currentFunction = Just mangledName}
                                (updatedEnv, compileValueFunc lambdaBody)
                            u -> (env, compileValueFunc u)
                    let ((retVal, stmts), st'') = runState (runWriterT (runReaderT action newEnv)) st'
                    let llvmFnArgTypes = map toAllocationLlvmType fnArgs
                    let llvmFnRetType = toAllocationLlvmType fnRetType
                    let llvmFnArgs = Map.fromList [(case argName of LlvmRegister _ n -> n; _ -> error "Expected LlvmRegister", argType) | (argName, argType) <- zip fnArgRegs llvmFnArgTypes]

                    let (finalRetVal, additionalStmts) = case getValueType retVal of
                            LlvmVoid -> (Nothing, [])
                            LlvmPointer innerType@(LlvmNamedType _) ->
                                if isADTReturnedByValue llvmFnRetType
                                    then
                                        let loadReg = LlvmRegister innerType ("reg_" ++ show (nextRegister st''))
                                            loadStmt = LlvmAssign (getRegName loadReg) (LlvmLoad retVal)
                                        in (Just loadReg, [loadStmt])
                                    else
                                        (Just retVal, [])
                            _ -> (Just retVal, [])

                    let finalStatement = LlvmRet llvmFnRetType finalRetVal

                    put st''{nextRegister = nextRegister st'' + length additionalStmts}

                    let llvmFunction =
                            LlvmFunction
                                { functionName = mangledName
                                , functionParams = llvmFnArgs
                                , functionReturnType = llvmFnRetType
                                , functionBlocks = []
                                , functionStatements = stmts ++ additionalStmts ++ [finalStatement]
                                }
                    modify $ \s -> s{irFunctions = llvmFunction : irFunctions s}

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

isADTReturnedByValue :: LlvmType -> Bool
isADTReturnedByValue (LlvmNamedType _) = True
isADTReturnedByValue (LlvmPointer _) = False
isADTReturnedByValue _ = False

getRegName :: LlvmValue -> String
getRegName (LlvmRegister _ name) = name
getRegName _ = error "Expected register"
