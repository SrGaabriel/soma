{-# LANGUAGE TupleSections #-}

module Metal.Gen.Binding where

import Decisions.Model (patternMatchArity)
import Metal.Expr (MetallicExpr (..))
import Metal.Function
import Metal.Gen.Core (MetalGen, addFunction, MetalScope (MetalScope), withScope)
import Metal.Gen.Value (metallizeValue)
import Syntax.Tree (Expr (..))
import Typing.Currying (uncurryFunction)
import Typing.Types
import qualified Data.Map as Map

metallizeBinding :: Expr -> MetalGen ()
metallizeBinding (ExprBindingDef name (Forall typeVars constraints bindingTyp) body _ _) = do
    let (paramTypes, retType) = uncurryFunction bindingTyp

    (paramNames, metalBody) <- metallizeFnBody name body paramTypes
    let params = zip paramNames paramTypes

    let func =
            if null typeVars && null constraints
                then
                    MMonomorphic
                        { mfName = name
                        , mfParams = params
                        , mfReturnType = retType
                        , mfBody = metalBody
                        }
                else
                    MPolymorphic
                        { mfName = name
                        , mfTypeParams = typeVars
                        , mfConstraints = constraints
                        , mfParams = params
                        , mfReturnType = retType
                        , mfBody = metalBody
                        }

    addFunction name func
metallizeBinding _ = return ()

metallizeFnBody :: String -> Expr -> [Type] -> MetalGen ([String], MetallicExpr)
metallizeFnBody fnName (ExprLambda paramNames body _) paramTypes = do
    let argBindings = zip paramNames paramTypes
    let newScope = MetalScope fnName (Map.fromList [(name, typ) | (name, typ) <- argBindings]) Nothing
    metalBody <- withScope newScope $ metallizeValue body
    return (paramNames, metalBody)
metallizeFnBody _ body@(ExprDerivedPatternMatch _arms) paramTypes = do
    let arity = patternMatchArity body
        paramNames = ["arg" ++ show i | i <- [0 .. arity - 1]]

    let _scrutinees =
            [ MVar paramName paramType
            | (paramName, paramType) <- zip paramNames paramTypes
            ]

    metalBody <- error "TODO: metallize derived pattern match body"

    return (paramNames, metalBody)
metallizeFnBody _ body _ = ([],) <$> metallizeValue body
