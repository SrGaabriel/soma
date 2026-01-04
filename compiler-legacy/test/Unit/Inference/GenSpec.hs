{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Unit.Inference.GenSpec (spec) where

import Test.Hspec
import Typing.Types

spec :: Spec
spec = describe "Inference.Gen" $ do
    describe "type construction" $ do
        it "creates int type" $ do
            intType `shouldBe` TConstructor (TypeConstructor (TyPrim TPInt) KindStar)

        it "creates bool type" $ do
            boolType `shouldBe` TConstructor (TypeConstructor (TyPrim TPBool) KindStar)

        it "creates string type" $ do
            strType `shouldBe` TConstructor (TypeConstructor (TyPrim TPString) KindStar)

        it "creates unit type" $ do
            unitType `shouldBe` TConstructor (TypeConstructor (TyPrim TPUnit) KindStar)

        it "creates function type" $ do
            let funTy = TArrow intType boolType
            isFunctionType funTy `shouldBe` True

        it "creates array type" $ do
            let arrTy = arrayType intType
            isArrayType arrTy `shouldBe` True

    describe "type predicates" $ do
        it "identifies function types" $ do
            isFunctionType (TArrow intType intType) `shouldBe` True
            isFunctionType intType `shouldBe` False

        it "identifies array types" $ do
            isArrayType (arrayType intType) `shouldBe` True
            isArrayType intType `shouldBe` False

    describe "function type splitting" $ do
        it "splits simple function type" $ do
            let funTy = TArrow intType boolType
            splitFunctionType 1 funTy `shouldBe` ([intType], boolType)

        it "returns empty args for non-function" $ do
            splitFunctionType 1 intType `shouldBe` ([], intType)

        it "splits curried function correctly" $ do
            let funTy = TArrow intType (TArrow boolType strType)
            splitFunctionType 1 funTy `shouldBe` ([intType], TArrow boolType strType)
            splitFunctionType 2 funTy `shouldBe` ([intType, boolType], strType)

    describe "tuple types" $ do
        it "creates empty tuple as unit" $ do
            tupleType [] `shouldBe` unitType

        it "creates pair type" $ do
            let pairTy = tupleType [intType, boolType]
            pairTy `shouldSatisfy` \case
                TApp _ _ -> True
                _ -> False

    describe "qualified types" $ do
        it "creates clean qualified type" $ do
            let qual = cleanQualified intType
            qual `shouldBe` Forall [] [] intType

        it "extracts type from qualified" $ do
            let Forall _ _ ty = cleanQualified intType
            ty `shouldBe` intType

    describe "constraint operations" $ do
        it "extracts constraint class name" $ do
            let showConstraint = Constraint (TApp (TUnresolved "Show") intType)
            constraintClassName showConstraint `shouldBe` "Show"

        it "extracts constraint types" $ do
            let showConstraint = Constraint (TApp (TUnresolved "Show") intType)
            constraintTypes showConstraint `shouldBe` [intType]

    describe "arity counting" $ do
        it "counts arity of simple type as 0" $ do
            countArityFromType intType `shouldBe` 0

        it "counts arity of unary function as 1" $ do
            countArityFromType (TArrow intType intType) `shouldBe` 1

        it "counts arity of binary function as 2" $ do
            countArityFromType (TArrow intType (TArrow intType intType)) `shouldBe` 2

        it "counts arity of ternary function as 3" $ do
            let ty = TArrow intType (TArrow intType (TArrow intType intType))
            countArityFromType ty `shouldBe` 3
