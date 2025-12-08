{-# LANGUAGE OverloadedStrings #-}

module Unit.Inference.SolvingSpec (spec) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Inference.Core (UnificationPurpose (..))
import Inference.Solving
import Inference.Substitution
import Lexing.Position (Span (..))
import Test.Hspec
import Typing.Types

-- Helper to create a type variable
mkTyVar :: String -> TyVar
mkTyVar name = TypeVar name KindStar

-- Helper span for testing
testSpan :: Span
testSpan = Span 0 0

spec :: Spec
spec = describe "Inference.Solving" $ do
    describe "unifyTypes" $ do
        describe "identical types" $ do
            it "unifies Int with Int" $ do
                let result = unifyTypes testSpan UnifyFunctionApplication intType intType
                result `shouldBe` Right Map.empty

            it "unifies Bool with Bool" $ do
                let result = unifyTypes testSpan UnifyFunctionApplication boolType boolType
                result `shouldBe` Right Map.empty

            it "unifies String with String" $ do
                let result = unifyTypes testSpan UnifyFunctionApplication strType strType
                result `shouldBe` Right Map.empty

        describe "type variables" $ do
            it "unifies type variable with concrete type" $ do
                let tvar = TVar (mkTyVar "a")
                let result = unifyTypes testSpan UnifyFunctionApplication tvar intType
                case result of
                    Right subst -> Map.lookup (mkTyVar "a") subst `shouldBe` Just intType
                    Left _ -> expectationFailure "Expected successful unification"

            it "unifies concrete type with type variable" $ do
                let tvar = TVar (mkTyVar "a")
                let result = unifyTypes testSpan UnifyFunctionApplication intType tvar
                case result of
                    Right subst -> Map.lookup (mkTyVar "a") subst `shouldBe` Just intType
                    Left _ -> expectationFailure "Expected successful unification"

            it "unifies two different type variables" $ do
                let tvar1 = TVar (mkTyVar "a")
                let tvar2 = TVar (mkTyVar "b")
                let result = unifyTypes testSpan UnifyFunctionApplication tvar1 tvar2
                case result of
                    Right subst -> Map.size subst `shouldBe` 1
                    Left _ -> expectationFailure "Expected successful unification"

            it "unifies type variable with itself" $ do
                let tvar = TVar (mkTyVar "a")
                let result = unifyTypes testSpan UnifyFunctionApplication tvar tvar
                result `shouldBe` Right Map.empty

        describe "function types" $ do
            it "unifies identical function types" $ do
                let funTy = TArrow intType boolType
                let result = unifyTypes testSpan UnifyFunctionApplication funTy funTy
                result `shouldBe` Right Map.empty

            it "unifies function types with type variables" $ do
                let tvar = TVar (mkTyVar "a")
                let funTy1 = TArrow tvar boolType
                let funTy2 = TArrow intType boolType
                let result = unifyTypes testSpan UnifyFunctionApplication funTy1 funTy2
                case result of
                    Right subst -> Map.lookup (mkTyVar "a") subst `shouldBe` Just intType
                    Left _ -> expectationFailure "Expected successful unification"

            it "unifies nested function types" $ do
                let tvar = TVar (mkTyVar "a")
                let funTy1 = TArrow intType (TArrow tvar boolType)
                let funTy2 = TArrow intType (TArrow strType boolType)
                let result = unifyTypes testSpan UnifyFunctionApplication funTy1 funTy2
                case result of
                    Right subst -> Map.lookup (mkTyVar "a") subst `shouldBe` Just strType
                    Left _ -> expectationFailure "Expected successful unification"

        describe "type application" $ do
            it "unifies identical type applications" $ do
                let arrTy = arrayType intType
                let result = unifyTypes testSpan UnifyFunctionApplication arrTy arrTy
                result `shouldBe` Right Map.empty

            it "unifies type applications with type variables" $ do
                let tvar = TVar (mkTyVar "a")
                let arrTy1 = arrayType tvar
                let arrTy2 = arrayType intType
                let result = unifyTypes testSpan UnifyFunctionApplication arrTy1 arrTy2
                case result of
                    Right subst -> Map.lookup (mkTyVar "a") subst `shouldBe` Just intType
                    Left _ -> expectationFailure "Expected successful unification"

        describe "failure cases" $ do
            it "fails to unify Int with Bool" $ do
                let result = unifyTypes testSpan UnifyFunctionApplication intType boolType
                case result of
                    Left _ -> pure ()
                    Right _ -> expectationFailure "Expected unification failure"

            it "fails to unify Int with String" $ do
                let result = unifyTypes testSpan UnifyFunctionApplication intType strType
                case result of
                    Left _ -> pure ()
                    Right _ -> expectationFailure "Expected unification failure"

            it "fails to unify function with non-function" $ do
                let funTy = TArrow intType intType
                let result = unifyTypes testSpan UnifyFunctionApplication funTy intType
                case result of
                    Left _ -> pure ()
                    Right _ -> expectationFailure "Expected unification failure"

            it "detects occurs check violation" $ do
                let tvar = TVar (mkTyVar "a")
                let cyclicTy = TArrow tvar tvar -- a -> a is fine
                let result1 = unifyTypes testSpan UnifyFunctionApplication tvar cyclicTy
                -- This should fail because we're trying to unify 'a' with 'a -> a'
                -- which would create infinite type a = a -> a
                case result1 of
                    Left errs -> length errs `shouldSatisfy` (> 0)
                    Right _ -> expectationFailure "Expected occurs check failure"

    describe "substitution" $ do
        it "applies empty substitution" $ do
            apply Map.empty intType `shouldBe` intType

        it "applies substitution to type variable" $ do
            let subst = Map.singleton (mkTyVar "a") intType
            apply subst (TVar (mkTyVar "a")) `shouldBe` intType

        it "applies substitution to function type" $ do
            let subst = Map.singleton (mkTyVar "a") intType
            let funTy = TArrow (TVar (mkTyVar "a")) boolType
            apply subst funTy `shouldBe` TArrow intType boolType

        it "applies substitution recursively" $ do
            let subst = Map.singleton (mkTyVar "a") intType
            let nestedTy = TArrow (TVar (mkTyVar "a")) (TArrow (TVar (mkTyVar "a")) boolType)
            apply subst nestedTy `shouldBe` TArrow intType (TArrow intType boolType)

        it "composes substitutions correctly" $ do
            let subst1 = Map.singleton (mkTyVar "a") (TVar (mkTyVar "b"))
            let subst2 = Map.singleton (mkTyVar "b") intType
            let composed = composeSubst subst2 subst1
            apply composed (TVar (mkTyVar "a")) `shouldBe` intType

    describe "free type variables" $ do
        it "finds no free variables in concrete type" $ do
            ftv intType `shouldBe` Set.empty

        it "finds free variable in type variable" $ do
            ftv (TVar (mkTyVar "a")) `shouldBe` Set.singleton (mkTyVar "a")

        it "finds free variables in function type" $ do
            let funTy = TArrow (TVar (mkTyVar "a")) (TVar (mkTyVar "b"))
            ftv funTy `shouldBe` Set.fromList [mkTyVar "a", mkTyVar "b"]

        it "finds free variables in nested type" $ do
            let nestedTy = TArrow intType (TArrow (TVar (mkTyVar "a")) boolType)
            ftv nestedTy `shouldBe` Set.singleton (mkTyVar "a")
