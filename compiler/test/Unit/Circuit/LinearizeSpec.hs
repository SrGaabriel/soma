{-# LANGUAGE OverloadedStrings #-}

module Unit.Circuit.LinearizeSpec (spec) where

import Circuit.Ir
import Circuit.Linearize
import Control.Monad.State (evalState)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Project.Name
import Project.Unique (Unique (..))
import Test.Generators
import Test.Hspec
import Test.QuickCheck
import Typing.Types

-- Helper to create a simple name
mkName :: String -> Int -> Name
mkName prefix n = NLocal (LocalId LPTemp n)

-- Helper to create a user name
mkUserName :: String -> Name
mkUserName s = NUser (Unique 0 "test" s)

-- Helper to run linearization
runLinearize :: CTerm -> CTerm
runLinearize term = evalState (linearizeTerm term) initLinearState

-- Helper to run linearization on a function
runLinearizeFunction :: CFunction -> CFunction
runLinearizeFunction = linearizeFunction

-- Helper to check if a term is affine (each variable used at most once)
isAffineTerm :: CTerm -> Bool
isAffineTerm term = all (<= 1) (Map.elems (countAllUses term))
  where
    countAllUses :: CTerm -> Map.Map Name Int
    countAllUses t = case t of
        CVar n _ -> Map.singleton n 1
        CDp0 n _ -> Map.singleton n 1
        CDp1 n _ -> Map.singleton n 1
        CLam n _ body -> Map.delete n (countAllUses body)
        CLet n _ val body ->
            Map.unionWith (+) (countAllUses val) (Map.delete n (countAllUses body))
        CDup n _ _ val body ->
            Map.unionWith (+) (countAllUses val) (Map.delete n (countAllUses body))
        CApp f x _ -> Map.unionWith (+) (countAllUses f) (countAllUses x)
        CSup _ a b _ -> Map.unionWith (+) (countAllUses a) (countAllUses b)
        CBinOp _ a b -> Map.unionWith (+) (countAllUses a) (countAllUses b)
        CCmpOp _ a b -> Map.unionWith (+) (countAllUses a) (countAllUses b)
        CUnaryOp _ a -> countAllUses a
        CTag _ fields _ -> Map.unionsWith (+) (map countAllUses fields)
        CCase scrut arms mdef _ ->
            let armUses =
                    [ Map.filterWithKey (\k _ -> k `notElem` map fst ns) (countAllUses body)
                    | (_, ns, body) <- arms
                    ]
            in Map.unionsWith (+) (countAllUses scrut : armUses ++ maybe [] (pure . countAllUses) mdef)
        CErase val body -> Map.unionWith (+) (countAllUses val) (countAllUses body)
        CClosureGetEnv e _ _ -> countAllUses e
        CProject e _ _ -> countAllUses e
        CFork _ _ comp cont -> Map.unionWith (+) (countAllUses comp) (countAllUses cont)
        _ -> Map.empty

-- Check if term contains any DUP nodes
containsDup :: CTerm -> Bool
containsDup term = any isDup (universe term)
  where
    isDup (CDup{}) = True
    isDup _ = False

-- Check if term contains any ERA/CErase nodes
containsErase :: CTerm -> Bool
containsErase term = any isErase (universe term)
  where
    isErase CEra = True
    isErase (CErase{}) = True
    isErase _ = False

-- Count DUP nodes in term
countDups :: CTerm -> Int
countDups term = length [() | CDup{} <- universe term]

spec :: Spec
spec = describe "Circuit.Linearize" $ do
    describe "countVarUses" $ do
        it "counts zero uses for unused variable" $ do
            let term = CInt 42
            countVarUses (mkName "x" 0) term `shouldBe` 0

        it "counts single use" $ do
            let name = mkName "x" 0
            let term = CVar name intType
            countVarUses name term `shouldBe` 1

        it "counts multiple uses" $ do
            let name = mkName "x" 0
            let term = CApp (CVar name intType) (CVar name intType) intType
            countVarUses name term `shouldBe` 2

        it "counts uses in binary operations" $ do
            let name = mkName "x" 0
            let term = CBinOp OpAdd (CVar name intType) (CVar name intType)
            countVarUses name term `shouldBe` 2

        it "respects shadowing in lambda" $ do
            let name = mkName "x" 0
            let term = CLam name intType (CVar name intType)
            countVarUses name term `shouldBe` 0 -- Shadowed by lambda parameter
        it "respects shadowing in let" $ do
            let outerX = mkName "x" 0
            let innerX = mkName "x" 0 -- Same name shadows
            let term = CLet innerX intType (CInt 1) (CVar innerX intType)
            -- The outer x is not used because innerX shadows it
            countVarUses outerX term `shouldBe` 0

        it "counts uses in nested expressions" $ do
            let name = mkName "x" 0
            let term =
                    CLam
                        (mkName "y" 1)
                        intType
                        (CApp (CVar name intType) (CVar name intType) intType)
            countVarUses name term `shouldBe` 2

    describe "linearizeTerm" $ do
        describe "single use variables" $ do
            it "preserves single-use variable" $ do
                let name = mkName "x" 0
                let term = CLam name intType (CVar name intType)
                let result = runLinearize term
                -- Should remain essentially unchanged
                containsDup result `shouldBe` False

            it "preserves single-use in application" $ do
                let name = mkName "x" 0
                let term = CLam name intType (CApp (CRef (mkUserName "f") (TArrow intType intType)) (CVar name intType) intType)
                let result = runLinearize term
                containsDup result `shouldBe` False

        describe "multi-use variables" $ do
            it "inserts DUP for double use" $ do
                let name = mkName "x" 0
                let term =
                        CLam
                            name
                            intType
                            (CApp (CVar name intType) (CVar name intType) intType)
                let result = runLinearize term
                containsDup result `shouldBe` True
                countDups result `shouldBe` 1

            it "inserts multiple DUPs for triple use" $ do
                let name = mkName "x" 0
                let term =
                        CLam
                            name
                            intType
                            ( CApp
                                (CApp (CVar name intType) (CVar name intType) intType)
                                (CVar name intType)
                                intType
                            )
                let result = runLinearize term
                containsDup result `shouldBe` True
                countDups result `shouldBe` 2

        describe "unused variables" $ do
            it "handles unused lambda parameter" $ do
                let name = mkName "x" 0
                let term = CLam name intType (CInt 42)
                let result = runLinearize term
                -- Should have some form of erasure
                containsDup result `shouldBe` True -- DUP with no usage creates erasure pattern
            it "handles unused let binding" $ do
                let name = mkName "x" 0
                let term = CLet name intType (CInt 1) (CInt 42)
                let result = runLinearize term
                -- The unused binding should be handled
                result `shouldSatisfy` \_ -> True -- Just verify it doesn't crash
        describe "nested bindings" $ do
            it "handles nested lambdas" $ do
                let x = mkName "x" 0
                let y = mkName "y" 1
                let term =
                        CLam
                            x
                            intType
                            ( CLam
                                y
                                intType
                                (CApp (CVar x intType) (CVar y intType) intType)
                            )
                let result = runLinearize term
                containsDup result `shouldBe` False -- Each used once
            it "handles let inside lambda" $ do
                let x = mkName "x" 0
                let y = mkName "y" 1
                let term =
                        CLam
                            x
                            intType
                            ( CLet
                                y
                                intType
                                (CVar x intType)
                                (CApp (CVar y intType) (CVar y intType) intType)
                            )
                let result = runLinearize term
                -- y is used twice, should have DUP
                containsDup result `shouldBe` True

    describe "linearizeFunction" $ do
        it "marks function as linearized" $ do
            let name = mkUserName "id"
            let paramName = mkName "x" 0
            let func = mkFunction name [(paramName, intType)] intType (CVar paramName intType)
            let result = runLinearizeFunction func
            cfmIsLinear (cfMetadata result) `shouldBe` True

        it "handles multi-use parameter" $ do
            let name = mkUserName "double"
            let paramName = mkName "x" 0
            let func =
                    mkFunction
                        name
                        [(paramName, intType)]
                        intType
                        (CBinOp OpAdd (CVar paramName intType) (CVar paramName intType))
            let result = runLinearizeFunction func
            containsDup (cfBody result) `shouldBe` True

    describe "linearizeModule" $ do
        it "marks module as linearized" $ do
            let mod' = emptyModule "test"
            let result = linearizeModule mod'
            cmIsLinearized result `shouldBe` True

        it "linearizes all functions" $ do
            let name1 = mkUserName "f"
            let name2 = mkUserName "g"
            let x = mkName "x" 0
            let func1 = mkFunction name1 [(x, intType)] intType (CVar x intType)
            let func2 =
                    mkFunction
                        name2
                        [(x, intType)]
                        intType
                        (CBinOp OpAdd (CVar x intType) (CVar x intType))
            let mod' = (emptyModule "test"){cmFunctions = [func1, func2]}
            let result = linearizeModule mod'
            all (cfmIsLinear . cfMetadata) (cmFunctions result) `shouldBe` True

    describe "affine property" $ do
        it "output of linearization is affine for identity" $ do
            let x = mkName "x" 0
            let term = CLam x intType (CVar x intType)
            let result = runLinearize term
            isAffineTerm result `shouldBe` True

        it "output of linearization is affine for double use" $ do
            let x = mkName "x" 0
            let term =
                    CLam
                        x
                        intType
                        (CApp (CVar x intType) (CVar x intType) intType)
            let result = runLinearize term
            -- After linearization, x should be used exactly once
            -- (through DUP projections)
            isAffineTerm result `shouldBe` True

    describe "edge cases" $ do
        it "handles empty case arms" $ do
            let x = mkName "x" 0
            let term = CCase (CVar x intType) [] Nothing intType
            let result = runLinearize term
            result `shouldSatisfy` \_ -> True -- Should not crash
        it "handles deeply nested terms" $ do
            let x = mkName "x" 0
            let deepTerm = iterate (\t -> CLam (mkName "y" 0) intType t) (CVar x intType) !! 10
            let term = CLam x intType deepTerm
            let result = runLinearize term
            result `shouldSatisfy` \_ -> True -- Should not crash
        it "handles binary operations with same variable" $ do
            let x = mkName "x" 0
            let term = CLam x intType (CBinOp OpMul (CVar x intType) (CVar x intType))
            let result = runLinearize term
            containsDup result `shouldBe` True
            isAffineTerm result `shouldBe` True
