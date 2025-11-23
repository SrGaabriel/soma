{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Metal.Gen.Binding where

import Alloy.Decisions (patternMatchArity)
import Control.Monad (foldM, forM)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Metal.Expr (MCaseArm (..), MetallicExpr (..))
import Metal.Function (MetallicFunction (..))
import Metal.Gen.Core (
    MetalGen,
    MetalScope (MetalScope),
    addFunction,
    getExprType,
    withScope,
 )
import Metal.Gen.Value (metallizeValue)
import Metal.Metadata (MetallicFunctionMetadata (..))
import Syntax.Tree (Expr (..), exprChildren)
import Typing.Currying (uncurryFunction)
import Typing.Types (QualifiedType (Forall), Type)
import Metal.Lift (collectBinders)

metallizeBinding :: Expr -> MetalGen ()
metallizeBinding (ExprBindingDef name (Forall typeVars constraints bindingTyp) body _isImpl _span) = do
    let (paramTypes, retType) = uncurryFunction bindingTyp

    (paramNames, metalBody) <- metallizeFnBody name body paramTypes retType

    let params = zip paramNames paramTypes

    let func =
            MetallicFunction
                { mfName = name
                , mfParams = params
                , mfReturnType = retType
                , mfBody = metalBody
                , mfMetadata =
                    MetallicFunctionMetadata
                        { mfmOriginalName = typeVars
                        , mfmConstraints = constraints
                        , mfmInstanceInfo = Nothing
                        }
                }

    addFunction name func
metallizeBinding _ = pure ()

metallizeFnBody :: String -> Expr -> [Type] -> Type -> MetalGen ([String], MetallicExpr)
metallizeFnBody fnName (ExprLambda paramNames body _) paramTypes _retType = do
    let argBindings = zip paramNames paramTypes
        newScope = MetalScope fnName (Map.fromList argBindings) Nothing
    metalBody <- withScope newScope $ metallizeValue body
    pure (paramNames, metalBody)
metallizeFnBody fnName body@(ExprDerivedPatternMatch arms) paramTypes retType = do
    let arity = patternMatchArity body
        paramNames = ["arg" ++ show i | i <- [0 .. arity - 1]]
        argBindings = zip paramNames paramTypes
        baseScope = MetalScope fnName (Map.fromList argBindings) Nothing

        scrutinees =
            [ MVar paramName paramType
            | (paramName, paramType) <- argBindings
            ]

    mArms <-
        forM arms $ \case
            ExprPatternMatchArm pats armBody _ -> do
                let binderNames = concatMap collectBinders pats
                binderTypes <- inferBinderTypesFromBody binderNames armBody
                let armScope = MetalScope (fnName ++ ".arm") binderTypes (Just baseScope)
                mBody <- withScope armScope $ metallizeValue armBody
                pure MCaseArm{mcaPatterns = pats, mcaBody = mBody}
            _ -> error "Invalid pattern match arm in derived pattern match"

    pure (paramNames, MCase scrutinees mArms Nothing retType)
metallizeFnBody _fnName body _paramTypes _retType = ([],) <$> metallizeValue body

inferBinderTypesFromBody :: [String] -> Expr -> MetalGen (Map.Map String Type)
inferBinderTypesFromBody names = go Map.empty
  where
    wanted = Set.fromList names
    go :: Map.Map String Type -> Expr -> MetalGen (Map.Map String Type)
    go acc e = do
        acc' <- case e of
            ExprUVar v _ | v `Set.member` wanted && Map.notMember v acc -> do
                ty <- getExprType e
                pure (Map.insert v ty acc)
            _ -> pure acc
        foldM go acc' (exprChildren e)
