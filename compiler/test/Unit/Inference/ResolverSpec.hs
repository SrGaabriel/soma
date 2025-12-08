{-# LANGUAGE OverloadedStrings #-}

module Unit.Inference.ResolverSpec (spec) where

import qualified Data.Map as Map
import Lexing.Position (Span (..))
import Project.Symbols
import Project.Unique
import Test.Hspec
import Typing.Types

spec :: Spec
spec = describe "Inference.Resolver" $ do
    describe "symbol creation" $ do
        it "creates unique identifiers" $ do
            let u1 = Unique 1 "test" "foo"
            let u2 = Unique 2 "test" "foo"
            u1 `shouldNotBe` u2

        it "preserves original name" $ do
            let u = Unique 1 "test" "myFunction"
            uniqueOriginal u `shouldBe` "myFunction"

        it "preserves module name" $ do
            let u = Unique 1 "myModule" "foo"
            uniqueModule u `shouldBe` "myModule"

    describe "symbol kinds" $ do
        it "distinguishes binding symbols" $ do
            let sym =
                    ResolvedSymbol
                        { resolvedSymbolUnique = Just (Unique 1 "test" "f")
                        , resolvedSymbolName = "f"
                        , resolvedSymbolKind = BindingSymbol (cleanQualified intType)
                        , resolvedSymbolModule = "test"
                        , resolvedSymbolPackage = "pkg"
                        , resolvedSymbolSpan = dummySpan
                        }
            case resolvedSymbolKind sym of
                BindingSymbol _ -> pure ()
                _ -> expectationFailure "Expected BindingSymbol"

        it "distinguishes data constructor symbols" $ do
            let sym =
                    ResolvedSymbol
                        { resolvedSymbolUnique = Just (Unique 1 "test" "Some")
                        , resolvedSymbolName = "Some"
                        , resolvedSymbolKind = DataConstructorSymbol "Option"
                        , resolvedSymbolModule = "test"
                        , resolvedSymbolPackage = "pkg"
                        , resolvedSymbolSpan = dummySpan
                        }
            case resolvedSymbolKind sym of
                DataConstructorSymbol parent -> parent `shouldBe` "Option"
                _ -> expectationFailure "Expected DataConstructorSymbol"

        it "distinguishes type symbols" $ do
            let sym =
                    ResolvedSymbol
                        { resolvedSymbolUnique = Just (Unique 1 "test" "Option")
                        , resolvedSymbolName = "Option"
                        , resolvedSymbolKind = TypeSymbol
                        , resolvedSymbolModule = "test"
                        , resolvedSymbolPackage = "pkg"
                        , resolvedSymbolSpan = dummySpan
                        }
            resolvedSymbolKind sym `shouldBe` TypeSymbol

    describe "type environment" $ do
        it "empty environment has no bindings" $ do
            let env = Map.empty :: Map.Map Symbol QualifiedType
            Map.size env `shouldBe` 0

        it "can insert and lookup bindings" $ do
            let sym =
                    ResolvedSymbol
                        { resolvedSymbolUnique = Just (Unique 1 "test" "x")
                        , resolvedSymbolName = "x"
                        , resolvedSymbolKind = BindingSymbol (cleanQualified intType)
                        , resolvedSymbolModule = "test"
                        , resolvedSymbolPackage = "pkg"
                        , resolvedSymbolSpan = dummySpan
                        }
            let env = Map.singleton sym (cleanQualified intType)
            Map.lookup sym env `shouldBe` Just (cleanQualified intType)

    describe "primitive type lookup" $ do
        it "finds Int primitive" $ do
            primitiveFromName "Int" `shouldBe` Just TPInt

        it "finds Bool primitive" $ do
            primitiveFromName "Bool" `shouldBe` Just TPBool

        it "finds String primitive" $ do
            primitiveFromName "String" `shouldBe` Just TPString

        it "finds Unit primitive" $ do
            primitiveFromName "Unit" `shouldBe` Just TPUnit
            primitiveFromName "()" `shouldBe` Just TPUnit

        it "finds Array primitive" $ do
            primitiveFromName "Array" `shouldBe` Just TPArray

        it "returns Nothing for unknown type" $ do
            primitiveFromName "Unknown" `shouldBe` Nothing

dummySpan :: Span
dummySpan = Span 0 0
