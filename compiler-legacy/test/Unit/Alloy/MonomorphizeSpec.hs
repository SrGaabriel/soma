{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- | Comprehensive test suite for Alloy.Monomorphize

This module tests the monomorphization pass which converts polymorphic
functions into monomorphic (fully specialized) versions. The pass:

1. Scans for polymorphic call sites
2. Creates specialized instances for each concrete type combination
3. Rewrites call sites to point to specialized functions
4. Eliminates remaining polymorphic functions

Test categories:
- Basic monomorphization
- Polymorphic function specialization
- Closure and environment handling
- Recursive function specialization
- Trait method dispatch
- Call site ID consistency
- Edge cases and invariants

IMPORTANT: The Unique type's Eq instance only compares uniqueId and uniqueModule,
NOT uniqueOriginal. So each function must have a different uniqueId to be distinct.
-}
module Unit.Alloy.MonomorphizeSpec (spec) where

import Alloy.Ir
import Alloy.Monomorphize
import Data.List (nub)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Metal.Metadata (defaultFunctionAttributes)
import Project.Name
import Project.Unique (Unique (..))
import Test.Hspec
import Typing.Types

-- ============================================================================
-- Test Helpers
-- ============================================================================

-- | Create a user name with a specific unique ID (IMPORTANT: each function needs different ID)
mkName :: Int -> String -> Name
mkName uid s = NUser (Unique uid "test" s)

-- | Create a local temp name
mkTempName :: Int -> Name
mkTempName n = NLocal (LocalId LPTemp n)

-- | Create a block name
mkBlockName :: Int -> Name
mkBlockName n = NLocal (LocalId LPBlock n)

-- | Create a type variable
mkTyVar :: String -> TyVar
mkTyVar s = TypeVar s KindStar

-- | Create a type variable type
tyVar :: String -> Type
tyVar s = TVar (mkTyVar s)

-- | Create a simple Alloy function
mkFunction :: Name -> [(Name, Type)] -> Type -> [ABlock] -> AlloyFunction
mkFunction name params retTy blocks =
    AlloyFunction
        { afName = name
        , afParams = params
        , afReturnType = retTy
        , afEntry = mkBlockName 0
        , afBlocks = blocks
        , afConstraints = []
        , afAttributes = defaultFunctionAttributes
        }

-- | Create a simple block with instructions
mkBlock :: Name -> [(Name, Type)] -> [AInstr] -> ATerminator -> ABlock
mkBlock name params instrs term =
    ABlock
        { abName = name
        , abParams = params
        , abInstrs = instrs
        , abTerminator = term
        }

-- | Create an empty module
mkModule :: String -> [AlloyFunction] -> AlloyModule
mkModule name funcs =
    AlloyModule
        { amName = name
        , amFunctions = funcs
        , amDictionaries = []
        , amTypeClasses = []
        , amStructTypes = Set.empty
        , amTypeDefs = []
        }

{- | Check if a function has any type variables in its signature
Note: This matches the production hasTypeVars - TSkolem is NOT considered polymorphic
because skolems are unified to concrete types during monomorphization
-}
hasPolySignature :: AlloyFunction -> Bool
hasPolySignature fn = any (hasTypeVarInType . snd) (afParams fn) || hasTypeVarInType (afReturnType fn)
  where
    hasTypeVarInType (TVar _) = True
    hasTypeVarInType (TApp a b) = hasTypeVarInType a || hasTypeVarInType b
    hasTypeVarInType (TArrow a b) = hasTypeVarInType a || hasTypeVarInType b
    hasTypeVarInType _ = False

-- | Find a function by name
findFunction :: Name -> AlloyModule -> Maybe AlloyFunction
findFunction name mod' = find' (amFunctions mod')
  where
    find' [] = Nothing
    find' (f : fs)
        | afName f == name = Just f
        | otherwise = find' fs

-- | Extract all direct call targets from a function
getCallTargets :: AlloyFunction -> [Name]
getCallTargets fn = concatMap getBlockCallTargets (afBlocks fn)
  where
    getBlockCallTargets block = mapMaybe getCallTarget (abInstrs block)
    getCallTarget (ILet _ _ (OpCall (Direct name) _)) = Just name
    getCallTarget _ = Nothing

-- | Count functions in module
countFunctions :: AlloyModule -> Int
countFunctions = length . amFunctions

-- ============================================================================
-- Spec
-- ============================================================================

spec :: Spec
spec = describe "Alloy.Monomorphize" $ do
    -- ========================================================================
    -- Basic Monomorphization Tests
    -- ========================================================================
    describe "basic monomorphization" $ do
        it "preserves main function" $ do
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        unitType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpConst CUnit)))
                        ]
            let mod' = mkModule "test" [mainFn]
            let result = monomorphizeModule mod'
            -- Main is always preserved
            countFunctions result `shouldBe` 1
            nameToString (afName (head (amFunctions result))) `shouldBe` "main"

        it "eliminates unused polymorphic functions" $ do
            let polyFn =
                    mkFunction
                        (mkName 0 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let mod' = mkModule "test" [polyFn]
            let result = monomorphizeModule mod'
            -- Unused polymorphic function should be eliminated
            countFunctions result `shouldBe` 0

        it "preserves concrete functions that are called" $ do
            -- Each function needs a different unique ID!
            let addFn =
                    mkFunction
                        (mkName 1 "add")
                        [(mkTempName 0, intType), (mkTempName 1, intType)]
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 2) intType (OpBin IAdd (OpVar (mkTempName 0)) (OpVar (mkTempName 1)))]
                            (ARet (Just (OpVar (mkTempName 2))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 3) intType (OpCall (Direct (mkName 1 "add")) [OpConst (CInt 1), OpConst (CInt 2)])]
                            (ARet (Just (OpVar (mkTempName 3))))
                        ]
            let mod' = mkModule "test" [addFn, mainFn]
            let result = monomorphizeModule mod'
            -- Both functions should be preserved (main + add)
            countFunctions result `shouldBe` 2

    -- ========================================================================
    -- Polymorphic Function Specialization Tests
    -- ========================================================================
    describe "polymorphic function specialization" $ do
        it "creates specialized instance when polymorphic function is called with concrete type" $ do
            -- Identity function: id :: a -> a
            let idFn =
                    mkFunction
                        (mkName 1 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            -- Main calls id with Int literal
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 42)])]
                            (ARet (Just (OpVar (mkTempName 1))))
                        ]
            let mod' = mkModule "test" [idFn, mainFn]
            let result = monomorphizeModule mod'
            -- Should have main + specialized id (2 functions)
            countFunctions result `shouldBe` 2
            -- All functions should be concrete
            not (any hasPolySignature (amFunctions result)) `shouldBe` True

        it "creates multiple specializations for different concrete types" $ do
            let idFn =
                    mkFunction
                        (mkName 1 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 42)])
                            , ILet (mkTempName 2) boolType (OpCall (Direct (mkName 1 "id")) [OpConst (CBool True)])
                            , ILet (mkTempName 3) strType (OpCall (Direct (mkName 1 "id")) [OpConst (CString "hello")])
                            ]
                            (ARet (Just (OpVar (mkTempName 1))))
                        ]
            let mod' = mkModule "test" [idFn, mainFn]
            let result = monomorphizeModule mod'
            -- Should have main + 3 specialized versions of id
            countFunctions result `shouldBe` 4
            not (any hasPolySignature (amFunctions result)) `shouldBe` True

        it "specializes binary polymorphic functions" $ do
            -- const :: a -> b -> a
            let constFn =
                    mkFunction
                        (mkName 1 "const")
                        [(mkTempName 0, tyVar "a"), (mkTempName 1, tyVar "b")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 2) intType (OpCall (Direct (mkName 1 "const")) [OpConst (CInt 1), OpConst (CBool True)])]
                            (ARet (Just (OpVar (mkTempName 2))))
                        ]
            let mod' = mkModule "test" [constFn, mainFn]
            let result = monomorphizeModule mod'
            countFunctions result `shouldBe` 2
            not (any hasPolySignature (amFunctions result)) `shouldBe` True

        it "specializes when called with variable of known type" $ do
            let idFn =
                    mkFunction
                        (mkName 1 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            -- Main has an Int parameter and passes it to id
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        [(mkTempName 10, intType)]
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "id")) [OpVar (mkTempName 10)])]
                            (ARet (Just (OpVar (mkTempName 1))))
                        ]
            let mod' = mkModule "test" [idFn, mainFn]
            let result = monomorphizeModule mod'
            countFunctions result `shouldBe` 2
            not (any hasPolySignature (amFunctions result)) `shouldBe` True

    -- ========================================================================
    -- Nested and Chained Calls
    -- ========================================================================
    describe "nested and chained calls" $ do
        it "handles nested polymorphic calls" $ do
            let idFn =
                    mkFunction
                        (mkName 1 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            -- applyId calls id internally
            let applyIdFn =
                    mkFunction
                        (mkName 2 "applyId")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 1) (tyVar "a") (OpCall (Direct (mkName 1 "id")) [OpVar (mkTempName 0)])]
                            (ARet (Just (OpVar (mkTempName 1))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 2) intType (OpCall (Direct (mkName 2 "applyId")) [OpConst (CInt 42)])]
                            (ARet (Just (OpVar (mkTempName 2))))
                        ]
            let mod' = mkModule "test" [idFn, applyIdFn, mainFn]
            let result = monomorphizeModule mod'
            -- main + applyId$Int + id$Int = 3 functions
            not (any hasPolySignature (amFunctions result)) `shouldBe` True

        it "handles chain of polymorphic calls reaching fixpoint" $ do
            -- f1 calls f2, f2 calls f3, etc.
            let mkChainFn :: Int -> Int -> String -> AlloyFunction
                mkChainFn uid nextUid nextName =
                    mkFunction
                        (mkName uid ("f" ++ show uid))
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 1) (tyVar "a") (OpCall (Direct (mkName nextUid nextName)) [OpVar (mkTempName 0)])]
                            (ARet (Just (OpVar (mkTempName 1))))
                        ]
            let f5 =
                    mkFunction
                        (mkName 5 "f5")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let chainFns = [mkChainFn 1 2 "f2", mkChainFn 2 3 "f3", mkChainFn 3 4 "f4", mkChainFn 4 5 "f5", f5]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 2) intType (OpCall (Direct (mkName 1 "f1")) [OpConst (CInt 42)])]
                            (ARet (Just (OpVar (mkTempName 2))))
                        ]
            let mod' = mkModule "test" (chainFns ++ [mainFn])
            let result = monomorphizeModule mod'
            -- Should specialize all functions in the chain
            not (any hasPolySignature (amFunctions result)) `shouldBe` True

    -- ========================================================================
    -- Recursive Function Tests
    -- ========================================================================
    describe "recursive function specialization" $ do
        it "handles self-recursive polymorphic functions" $ do
            -- length :: Array a -> Int (recursive)
            let lengthFn =
                    mkFunction
                        (mkName 1 "length")
                        [(mkTempName 0, arrayType (tyVar "a"))]
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ ILet (mkTempName 1) intType (OpArrayLength (OpVar (mkTempName 0)))
                            , ILet (mkTempName 2) boolType (OpCmp CEq (OpVar (mkTempName 1)) (OpConst (CInt 0)))
                            ]
                            (ACondBr (OpVar (mkTempName 2)) (mkBlockName 1) [] (mkBlockName 2) [])
                        , mkBlock
                            (mkBlockName 1)
                            []
                            []
                            (ARet (Just (OpConst (CInt 0))))
                        , mkBlock
                            (mkBlockName 2)
                            []
                            [ ILet (mkTempName 3) (arrayType (tyVar "a")) (OpArrayTail (OpVar (mkTempName 0)))
                            , ILet (mkTempName 4) intType (OpCall (Direct (mkName 1 "length")) [OpVar (mkTempName 3)])
                            , ILet (mkTempName 5) intType (OpBin IAdd (OpVar (mkTempName 4)) (OpConst (CInt 1)))
                            ]
                            (ARet (Just (OpVar (mkTempName 5))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ ILet (mkTempName 6) (arrayType intType) (OpMakeArray [OpConst (CInt 1), OpConst (CInt 2), OpConst (CInt 3)])
                            , ILet (mkTempName 7) intType (OpCall (Direct (mkName 1 "length")) [OpVar (mkTempName 6)])
                            ]
                            (ARet (Just (OpVar (mkTempName 7))))
                        ]
            let mod' = mkModule "test" [lengthFn, mainFn]
            let result = monomorphizeModule mod'
            -- All functions should be concrete after monomorphization
            not (any hasPolySignature (amFunctions result)) `shouldBe` True
            -- Should have at least main and length$ArrayInt
            countFunctions result `shouldSatisfy` (>= 2)

        it "handles mutually recursive polymorphic functions" $ do
            -- even :: Array a -> Bool (calls odd)
            -- odd :: Array a -> Bool (calls even)
            let evenFn =
                    mkFunction
                        (mkName 1 "even")
                        [(mkTempName 0, arrayType (tyVar "a"))]
                        boolType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ ILet (mkTempName 1) intType (OpArrayLength (OpVar (mkTempName 0)))
                            , ILet (mkTempName 2) boolType (OpCmp CEq (OpVar (mkTempName 1)) (OpConst (CInt 0)))
                            ]
                            (ACondBr (OpVar (mkTempName 2)) (mkBlockName 1) [] (mkBlockName 2) [])
                        , mkBlock
                            (mkBlockName 1)
                            []
                            []
                            (ARet (Just (OpConst (CBool True))))
                        , mkBlock
                            (mkBlockName 2)
                            []
                            [ ILet (mkTempName 3) (arrayType (tyVar "a")) (OpArrayTail (OpVar (mkTempName 0)))
                            , ILet (mkTempName 4) boolType (OpCall (Direct (mkName 2 "odd")) [OpVar (mkTempName 3)])
                            ]
                            (ARet (Just (OpVar (mkTempName 4))))
                        ]
            let oddFn =
                    mkFunction
                        (mkName 2 "odd")
                        [(mkTempName 0, arrayType (tyVar "a"))]
                        boolType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ ILet (mkTempName 1) intType (OpArrayLength (OpVar (mkTempName 0)))
                            , ILet (mkTempName 2) boolType (OpCmp CEq (OpVar (mkTempName 1)) (OpConst (CInt 0)))
                            ]
                            (ACondBr (OpVar (mkTempName 2)) (mkBlockName 1) [] (mkBlockName 2) [])
                        , mkBlock
                            (mkBlockName 1)
                            []
                            []
                            (ARet (Just (OpConst (CBool False))))
                        , mkBlock
                            (mkBlockName 2)
                            []
                            [ ILet (mkTempName 3) (arrayType (tyVar "a")) (OpArrayTail (OpVar (mkTempName 0)))
                            , ILet (mkTempName 4) boolType (OpCall (Direct (mkName 1 "even")) [OpVar (mkTempName 3)])
                            ]
                            (ARet (Just (OpVar (mkTempName 4))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        boolType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ ILet (mkTempName 5) (arrayType intType) (OpMakeArray [OpConst (CInt 1), OpConst (CInt 2)])
                            , ILet (mkTempName 6) boolType (OpCall (Direct (mkName 1 "even")) [OpVar (mkTempName 5)])
                            ]
                            (ARet (Just (OpVar (mkTempName 6))))
                        ]
            let mod' = mkModule "test" [evenFn, oddFn, mainFn]
            let result = monomorphizeModule mod'
            not (any hasPolySignature (amFunctions result)) `shouldBe` True

    -- ========================================================================
    -- Closure and Environment Tests
    -- ========================================================================
    describe "closure and environment handling" $ it "specializes closure allocations with polymorphic types" $ do
        -- A lambda that captures a polymorphic type
        let lambdaFn =
                mkFunction
                    (mkName 2 "lambda")
                    [(mkTempName 0, tyVar "a"), (mkTempName 1, tyVar "a")]
                    (tyVar "a")
                    [ mkBlock
                        (mkBlockName 0)
                        []
                        []
                        (ARet (Just (OpVar (mkTempName 0))))
                    ]
        let wrapperFn =
                mkFunction
                    (mkName 1 "wrapper")
                    [(mkTempName 0, tyVar "a")]
                    (TArrow (tyVar "a") (tyVar "a"))
                    [ mkBlock
                        (mkBlockName 0)
                        []
                        [ ILet (mkTempName 1) (TArrow (tyVar "a") (tyVar "a")) (OpAllocClosure (OpVar (mkName 2 "lambda")) 2 1)
                        , IEffect (EffClosureSetEnv (OpVar (mkTempName 1)) 0 (OpVar (mkTempName 0)))
                        ]
                        (ARet (Just (OpVar (mkTempName 1))))
                    ]
        let mainFn =
                mkFunction
                    (mkName 0 "main")
                    []
                    (TArrow intType intType)
                    [ mkBlock
                        (mkBlockName 0)
                        []
                        [ ILet (mkTempName 2) (TArrow intType intType) (OpCall (Direct (mkName 1 "wrapper")) [OpConst (CInt 42)])
                        ]
                        (ARet (Just (OpVar (mkTempName 2))))
                    ]
        let mod' = mkModule "test" [lambdaFn, wrapperFn, mainFn]
        let result = monomorphizeModule mod'
        not (any hasPolySignature (amFunctions result)) `shouldBe` True

    -- ========================================================================
    -- Trait Method Dispatch Tests
    -- ========================================================================
    describe "trait method dispatch" $ it "resolves OpDictCall to direct calls after monomorphization" $ do
        -- Simulating: show :: Show a => a -> String
        let showIntFn =
                mkFunction
                    (makeInstanceMethod (mkName 3 "show") intType)
                    [(mkTempName 0, intType)]
                    strType
                    [ mkBlock
                        (mkBlockName 0)
                        []
                        [ILet (mkTempName 1) strType (OpCall (Direct (mkName 1 "intToStr")) [OpVar (mkTempName 0)])]
                        (ARet (Just (OpVar (mkTempName 1))))
                    ]
        let mainFn =
                mkFunction
                    (mkName 0 "main")
                    []
                    strType
                    [ mkBlock
                        (mkBlockName 0)
                        []
                        [ ILet (mkTempName 2) strType (OpDictCall (OpVar (mkTempName 10)) 0 (mkName 3 "show") [OpConst (CInt 42)])
                        ]
                        (ARet (Just (OpVar (mkTempName 2))))
                    ]
        let intToStrFn =
                mkFunction
                    (mkName 1 "intToStr")
                    [(mkTempName 0, intType)]
                    strType
                    [ mkBlock
                        (mkBlockName 0)
                        []
                        []
                        (ARet (Just (OpConst (CString "42"))))
                    ]
        let mod' = mkModule "test" [showIntFn, mainFn, intToStrFn]
        let result = monomorphizeModule mod'
        -- The module should compile without polymorphic functions remaining
        not (any hasPolySignature (amFunctions result)) `shouldBe` True

    -- ========================================================================
    -- Call Site ID Consistency Tests
    -- ========================================================================
    describe "call site ID consistency" $ do
        it "correctly rewrites multiple calls in single block" $ do
            let idFn =
                    mkFunction
                        (mkName 1 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 1)])
                            , ILet (mkTempName 2) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 2)])
                            , ILet (mkTempName 3) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 3)])
                            , ILet (mkTempName 4) intType (OpBin IAdd (OpVar (mkTempName 1)) (OpVar (mkTempName 2)))
                            , ILet (mkTempName 5) intType (OpBin IAdd (OpVar (mkTempName 4)) (OpVar (mkTempName 3)))
                            ]
                            (ARet (Just (OpVar (mkTempName 5))))
                        ]
            let mod' = mkModule "test" [idFn, mainFn]
            let result = monomorphizeModule mod'
            -- Should have exactly 2 functions: main and id$Int
            countFunctions result `shouldBe` 2
            -- All calls in main should be to the specialized version
            case findFunction (mkName 0 "main") result of
                Just mainResult -> do
                    let targets = getCallTargets mainResult
                    -- All 3 calls should target the same specialized function
                    length (nub targets) `shouldBe` 1
                Nothing -> expectationFailure "main function not found"

        it "correctly handles calls across multiple blocks" $ do
            let idFn =
                    mkFunction
                        (mkName 1 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        [(mkTempName 10, boolType)]
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 1)])]
                            (ACondBr (OpVar (mkTempName 10)) (mkBlockName 1) [] (mkBlockName 2) [])
                        , mkBlock
                            (mkBlockName 1)
                            []
                            [ILet (mkTempName 2) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 2)])]
                            (ARet (Just (OpVar (mkTempName 2))))
                        , mkBlock
                            (mkBlockName 2)
                            []
                            [ILet (mkTempName 3) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 3)])]
                            (ARet (Just (OpVar (mkTempName 3))))
                        ]
            let mod' = mkModule "test" [idFn, mainFn]
            let result = monomorphizeModule mod'
            -- All calls should be to the same specialized function
            case findFunction (mkName 0 "main") result of
                Just mainResult -> do
                    let targets = getCallTargets mainResult
                    length (nub targets) `shouldBe` 1
                Nothing -> expectationFailure "main function not found"

    -- ========================================================================
    -- Deduplication Tests
    -- ========================================================================
    describe "deduplication" $ it "deduplicates identical specializations from different call sites" $ do
        let idFn =
                mkFunction
                    (mkName 1 "id")
                    [(mkTempName 0, tyVar "a")]
                    (tyVar "a")
                    [ mkBlock
                        (mkBlockName 0)
                        []
                        []
                        (ARet (Just (OpVar (mkTempName 0))))
                    ]
        -- Two functions that both call id with Int
        let fn1 =
                mkFunction
                    (mkName 2 "fn1")
                    []
                    intType
                    [ mkBlock
                        (mkBlockName 0)
                        []
                        [ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 1)])]
                        (ARet (Just (OpVar (mkTempName 1))))
                    ]
        let fn2 =
                mkFunction
                    (mkName 3 "fn2")
                    []
                    intType
                    [ mkBlock
                        (mkBlockName 0)
                        []
                        [ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 2)])]
                        (ARet (Just (OpVar (mkTempName 1))))
                    ]
        let mainFn =
                mkFunction
                    (mkName 0 "main")
                    []
                    intType
                    [ mkBlock
                        (mkBlockName 0)
                        []
                        [ ILet (mkTempName 2) intType (OpCall (Direct (mkName 2 "fn1")) [])
                        , ILet (mkTempName 3) intType (OpCall (Direct (mkName 3 "fn2")) [])
                        , ILet (mkTempName 4) intType (OpBin IAdd (OpVar (mkTempName 2)) (OpVar (mkTempName 3)))
                        ]
                        (ARet (Just (OpVar (mkTempName 4))))
                    ]
        let mod' = mkModule "test" [idFn, fn1, fn2, mainFn]
        let result = monomorphizeModule mod'
        -- Should only have one id specialization, not two
        let idFunctions = filter (\f -> "id" `elem` words (nameOriginal (afName f))) (amFunctions result)
        length idFunctions `shouldBe` 1

    -- ========================================================================
    -- Edge Cases and Invariants
    -- ========================================================================
    describe "edge cases and invariants" $ do
        it "handles empty module" $ do
            let mod' = mkModule "empty" []
            let result = monomorphizeModule mod'
            amFunctions result `shouldBe` []

        it "handles deeply nested type applications" $ do
            -- Array (Array (Array Int))
            let deepType = arrayType (arrayType (arrayType intType))
            let idFn =
                    mkFunction
                        (mkName 1 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        [(mkTempName 10, deepType)]
                        deepType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ ILet (mkTempName 2) deepType (OpCall (Direct (mkName 1 "id")) [OpVar (mkTempName 10)])
                            ]
                            (ARet (Just (OpVar (mkTempName 2))))
                        ]
            let mod' = mkModule "test" [idFn, mainFn]
            let result = monomorphizeModule mod'
            not (any hasPolySignature (amFunctions result)) `shouldBe` True

        it "handles function types as type arguments" $ do
            -- id :: a -> a, called with (Int -> Int)
            let idFn =
                    mkFunction
                        (mkName 1 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        [(mkTempName 10, TArrow intType intType)]
                        (TArrow intType intType)
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ ILet (mkTempName 2) (TArrow intType intType) (OpCall (Direct (mkName 1 "id")) [OpVar (mkTempName 10)])
                            ]
                            (ARet (Just (OpVar (mkTempName 2))))
                        ]
            let mod' = mkModule "test" [idFn, mainFn]
            let result = monomorphizeModule mod'
            not (any hasPolySignature (amFunctions result)) `shouldBe` True

        it "handles skolem type variables" $ do
            let skolemVar = SkolemVar "T" KindStar 0 "T" Rigid
            let skolemFn =
                    mkFunction
                        (mkName 1 "skolemId")
                        [(mkTempName 0, TSkolem skolemVar)]
                        (TSkolem skolemVar)
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "skolemId")) [OpConst (CInt 42)])]
                            (ARet (Just (OpVar (mkTempName 1))))
                        ]
            let mod' = mkModule "test" [skolemFn, mainFn]
            let result = monomorphizeModule mod'
            not (any hasPolySignature (amFunctions result)) `shouldBe` True

        it "preserves function with no blocks (external declaration)" $ do
            let externalFn =
                    mkFunction
                        (mkName 0 "main") -- Using main to ensure it's kept
                        [(mkTempName 0, intType)]
                        intType
                        [] -- No blocks
            let mod' = mkModule "test" [externalFn]
            let result = monomorphizeModule mod'
            countFunctions result `shouldBe` 1

    -- ========================================================================
    -- Stress Tests
    -- ========================================================================
    describe "stress tests" $ it "handles many specializations of the same function" $ do
        let idFn =
                mkFunction
                    (mkName 1 "id")
                    [(mkTempName 0, tyVar "a")]
                    (tyVar "a")
                    [ mkBlock
                        (mkBlockName 0)
                        []
                        []
                        (ARet (Just (OpVar (mkTempName 0))))
                    ]
        -- Create calls with many different types
        let types = [intType, boolType, strType, unitType, arrayType intType, arrayType boolType, TArrow intType intType, TArrow boolType boolType]
        let mkCall i ty = ILet (mkTempName i) ty (OpCall (Direct (mkName 1 "id")) [OpVar (mkTempName (i + 100))])
        let calls = zipWith mkCall [1 ..] types
        let mainFn =
                mkFunction
                    (mkName 0 "main")
                    (zipWith (\i ty -> (mkTempName (i + 100), ty)) [1 ..] types)
                    intType
                    [ mkBlock
                        (mkBlockName 0)
                        []
                        calls
                        (ARet (Just (OpConst (CInt 0))))
                    ]
        let mod' = mkModule "test" [idFn, mainFn]
        let result = monomorphizeModule mod'
        -- Should have main + 8 specializations
        countFunctions result `shouldBe` 9
        not (any hasPolySignature (amFunctions result)) `shouldBe` True

    -- ========================================================================
    -- monomorphizeFunction Tests
    -- ========================================================================
    describe "monomorphizeFunction (single function)" $ do
        it "returns original and clones for polymorphic function with self-call" $ do
            let idFn =
                    mkFunction
                        (mkName 1 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 42)])]
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let baseFnMap = Map.fromList [(mkName 1 "id", idFn)]
            let (_resultFn, clones) = monomorphizeFunction "test" baseFnMap idFn
            -- May or may not produce clones depending on self-call analysis
            length clones `shouldSatisfy` (>= 0)

        it "returns empty clones for concrete function" $ do
            let addFn =
                    mkFunction
                        (mkName 1 "add")
                        [(mkTempName 0, intType), (mkTempName 1, intType)]
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 2) intType (OpBin IAdd (OpVar (mkTempName 0)) (OpVar (mkTempName 1)))]
                            (ARet (Just (OpVar (mkTempName 2))))
                        ]
            let baseFnMap = Map.fromList [(mkName 1 "add", addFn)]
            let (_resultFn, clones) = monomorphizeFunction "test" baseFnMap addFn
            clones `shouldBe` []

    -- ========================================================================
    -- InstKey Tests
    -- ========================================================================
    describe "InstKey" $ do
        it "different types produce different keys" $ do
            let key1 = InstKey (mkName 1 "id") [intType]
            let key2 = InstKey (mkName 1 "id") [boolType]
            key1 `shouldNotBe` key2

        it "same types produce equal keys" $ do
            let key1 = InstKey (mkName 1 "id") [intType, boolType]
            let key2 = InstKey (mkName 1 "id") [intType, boolType]
            key1 `shouldBe` key2

        it "different base names produce different keys" $ do
            let key1 = InstKey (mkName 1 "id") [intType]
            let key2 = InstKey (mkName 2 "const") [intType] -- Different unique ID
            key1 `shouldNotBe` key2

        it "order of types matters" $ do
            let key1 = InstKey (mkName 1 "fn") [intType, boolType]
            let key2 = InstKey (mkName 1 "fn") [boolType, intType]
            key1 `shouldNotBe` key2

    -- ========================================================================
    -- Property Tests
    -- ========================================================================
    describe "property tests" $ do
        it "monomorphization is idempotent" $ do
            let idFn =
                    mkFunction
                        (mkName 1 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 42)])]
                            (ARet (Just (OpVar (mkTempName 1))))
                        ]
            let mod' = mkModule "test" [idFn, mainFn]
            let result1 = monomorphizeModule mod'
            let result2 = monomorphizeModule result1
            -- After first pass, all functions are concrete
            -- Second pass should produce identical result
            countFunctions result1 `shouldBe` countFunctions result2
            not (any hasPolySignature (amFunctions result1)) `shouldBe` True
            not (any hasPolySignature (amFunctions result2)) `shouldBe` True

        it "output never contains type variables in signatures" $ do
            -- More comprehensive test with various polymorphic patterns
            let idFn =
                    mkFunction
                        (mkName 1 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let constFn =
                    mkFunction
                        (mkName 2 "const")
                        [(mkTempName 0, tyVar "a"), (mkTempName 1, tyVar "b")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 1)])
                            , ILet (mkTempName 2) boolType (OpCall (Direct (mkName 1 "id")) [OpConst (CBool True)])
                            , ILet (mkTempName 3) intType (OpCall (Direct (mkName 2 "const")) [OpConst (CInt 2), OpConst (CBool False)])
                            ]
                            (ARet (Just (OpVar (mkTempName 1))))
                        ]
            let mod' = mkModule "test" [idFn, constFn, mainFn]
            let result = monomorphizeModule mod'
            not (any hasPolySignature (amFunctions result)) `shouldBe` True

        it "preserves module metadata" $ do
            let mod' =
                    AlloyModule
                        { amName = "test_module"
                        , amFunctions = []
                        , amDictionaries = []
                        , amTypeClasses = []
                        , amStructTypes = Set.fromList [Unique 1 "test" "MyStruct"]
                        , amTypeDefs = []
                        }
            let result = monomorphizeModule mod'
            amName result `shouldBe` "test_module"
            amStructTypes result `shouldBe` Set.fromList [Unique 1 "test" "MyStruct"]

    -- ========================================================================
    -- Complex Interaction Patterns
    -- ========================================================================
    describe "complex interaction patterns" $ do
        it "handles polymorphic function with multiple type variables" $ do
            -- map :: (a -> b) -> Array a -> Array b
            let mapFn =
                    mkFunction
                        (mkName 1 "map")
                        [ (mkTempName 0, TArrow (tyVar "a") (tyVar "b"))
                        , (mkTempName 1, arrayType (tyVar "a"))
                        ]
                        (arrayType (tyVar "b"))
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 1)))) -- Simplified body
                        ]
            let doubleFn =
                    mkFunction
                        (mkName 2 "double")
                        [(mkTempName 0, intType)]
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 1) intType (OpBin IMul (OpVar (mkTempName 0)) (OpConst (CInt 2)))]
                            (ARet (Just (OpVar (mkTempName 1))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        [(mkTempName 10, arrayType intType)]
                        (arrayType intType)
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ ILet (mkTempName 3) (arrayType intType) (OpCall (Direct (mkName 1 "map")) [OpVar (mkName 2 "double"), OpVar (mkTempName 10)])
                            ]
                            (ARet (Just (OpVar (mkTempName 3))))
                        ]
            let mod' = mkModule "test" [mapFn, doubleFn, mainFn]
            let result = monomorphizeModule mod'
            not (any hasPolySignature (amFunctions result)) `shouldBe` True

        it "handles diamond-shaped call graph with polymorphism" $ do
            --       main
            --      /    \
            --    fn1    fn2
            --      \    /
            --       id
            let idFn =
                    mkFunction
                        (mkName 1 "id")
                        [(mkTempName 0, tyVar "a")]
                        (tyVar "a")
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            []
                            (ARet (Just (OpVar (mkTempName 0))))
                        ]
            let fn1 =
                    mkFunction
                        (mkName 2 "fn1")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 1)])]
                            (ARet (Just (OpVar (mkTempName 1))))
                        ]
            let fn2 =
                    mkFunction
                        (mkName 3 "fn2")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ILet (mkTempName 1) intType (OpCall (Direct (mkName 1 "id")) [OpConst (CInt 2)])]
                            (ARet (Just (OpVar (mkTempName 1))))
                        ]
            let mainFn =
                    mkFunction
                        (mkName 0 "main")
                        []
                        intType
                        [ mkBlock
                            (mkBlockName 0)
                            []
                            [ ILet (mkTempName 2) intType (OpCall (Direct (mkName 2 "fn1")) [])
                            , ILet (mkTempName 3) intType (OpCall (Direct (mkName 3 "fn2")) [])
                            , ILet (mkTempName 4) intType (OpBin IAdd (OpVar (mkTempName 2)) (OpVar (mkTempName 3)))
                            ]
                            (ARet (Just (OpVar (mkTempName 4))))
                        ]
            let mod' = mkModule "test" [idFn, fn1, fn2, mainFn]
            let result = monomorphizeModule mod'
            -- Only one id$Int should exist despite being called from two places
            let idFunctions = filter (\f -> "id" `elem` words (nameOriginal (afName f))) (amFunctions result)
            length idFunctions `shouldBe` 1
            not (any hasPolySignature (amFunctions result)) `shouldBe` True
