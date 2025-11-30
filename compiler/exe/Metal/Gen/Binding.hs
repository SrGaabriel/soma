{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}

module Metal.Gen.Binding where

import Alloy.Decisions (patternMatchArity)
import Control.Monad (foldM, forM)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Lexing.Position (Located (..))
import Metal.Expr (MCaseArm (..), MetallicExpr (..))
import Metal.Function (MetallicFunction (..))
import Metal.Gen.Core (
    MetalGen,
    MetalScope (MetalScope),
    addFunction,
    getExprType,
    withScope,
 )
import Metal.Gen.Unique (sanitizeName)
import Metal.Gen.Value (metallizeValue)
import Metal.Lift (collectBinders)
import Metal.Metadata (MetallicFunctionMetadata (..))
import Project.Symbols (Symbol (..))
import Syntax.Tree (Expr (..), Modifier (..), exprChildren)
import Typing.Types (QualifiedType (Forall), Type (..))

-- | Get the arity (number of parameters) from a function body
getBodyArity :: Expr -> Int
getBodyArity (ExprLambda paramNames _ _) = length paramNames
getBodyArity body@(ExprDerivedPatternMatch _) = patternMatchArity body
getBodyArity _ = 0

{- | Split a function type into parameter types and return type based on arity
For example: splitFunctionType 1 (Int -> Int -> Int) = ([Int], Int -> Int)
-}
splitFunctionType :: Int -> Type -> ([Type], Type)
splitFunctionType 0 ty = ([], ty)
splitFunctionType n (TArrow argTy restTy) =
    let (args, ret) = splitFunctionType (n - 1) restTy
    in (argTy : args, ret)
splitFunctionType _ ty = ([], ty) -- Type doesn't have enough arrows

metallizeBinding :: Expr -> MetalGen ()
metallizeBinding (ExprBindingDef dirtyName (Located _ (Forall typeVars constraints bindingTyp)) body _isImpl mods _span) = do
    let name = sanitizeName dirtyName
    -- Get the actual arity from the body (lambda parameters or pattern match arity)
    let arity = getBodyArity body
    -- Split the type based on actual arity, not fully uncurrying
    let (paramTypes, retType) = splitFunctionType arity bindingTyp

    (paramNames, metalBody) <- metallizeFnBody name body paramTypes retType

    let params = zip paramNames paramTypes
    let isInline = ModInline `elem` mods

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
                        , mfmClosureInfo = Nothing
                        , mfmIsInline = isInline
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
            ExprVar (ResolvedSymbol{resolvedSymbolName}) _ | resolvedSymbolName `Set.member` wanted && Map.notMember resolvedSymbolName acc -> do
                ty <- getExprType e
                pure (Map.insert resolvedSymbolName ty acc)
            _ -> pure acc
        foldM go acc' (exprChildren e)
