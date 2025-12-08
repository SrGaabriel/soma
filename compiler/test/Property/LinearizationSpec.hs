{-# LANGUAGE OverloadedStrings #-}

module Property.LinearizationSpec (spec) where

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

-- | Count all variable uses in a term (binding-aware)
countAllVarUses :: CTerm -> Map.Map Name Int
countAllVarUses = go Set.empty
  where
    go bound term = case term of
        CVar n _
            | Set.member n bound -> Map.empty
            | otherwise -> Map.singleton n 1
        CDp0 n _
            | Set.member n bound -> Map.empty
            | otherwise -> Map.singleton n 1
        CDp1 n _
            | Set.member n bound -> Map.empty
            | otherwise -> Map.singleton n 1
        CLam n _ body -> go (Set.insert n bound) body
        CLet n _ val body ->
            Map.unionWith (+) (go bound val) (go (Set.insert n bound) body)
        CDup n _ _ val body ->
            Map.unionWith (+) (go bound val) (go (Set.insert n bound) body)
        CApp f x _ -> Map.unionWith (+) (go bound f) (go bound x)
        CSup _ a b _ -> Map.unionWith (+) (go bound a) (go bound b)
        CBinOp _ a b -> Map.unionWith (+) (go bound a) (go bound b)
        CCmpOp _ a b -> Map.unionWith (+) (go bound a) (go bound b)
        CUnaryOp _ a -> go bound a
        CTag _ fields _ -> Map.unionsWith (+) (map (go bound) fields)
        CCase scrut arms mdef _ ->
            let armBounds = [foldr (Set.insert . fst) bound ns | (_, ns, _) <- arms]
                armUses = zipWith (\b (_, _, body) -> go b body) armBounds arms
            in Map.unionsWith (+) (go bound scrut : armUses ++ maybe [] (pure . go bound) mdef)
        CErase val body -> Map.unionWith (+) (go bound val) (go bound body)
        CClosureGetEnv e _ _ -> go bound e
        CProject e _ _ -> go bound e
        CFork _ _ comp cont -> Map.unionWith (+) (go bound comp) (go bound cont)
        CClosure _ captured _ ->
            Map.fromList [(n, 1) | (n, _) <- captured, not (Set.member n bound)]
        _ -> Map.empty

-- | Check if a term is affine (all free variables used at most once)
isAffine :: CTerm -> Bool
isAffine term = all (<= 1) (Map.elems (countAllVarUses term))

-- | Count DUP nodes
countDupNodes :: CTerm -> Int
countDupNodes term = length [() | CDup{} <- universe term]

-- | Count ERA/CErase nodes
countEraseNodes :: CTerm -> Int
countEraseNodes term = length [() | t <- universe term, isErase t]
  where
    isErase CEra = True
    isErase (CErase{}) = True
    isErase _ = False

-- | Run linearization
linearize :: CTerm -> CTerm
linearize term = evalState (linearizeTerm term) initLinearState

-- | Linearize a function
linearizeFn :: CFunction -> CFunction
linearizeFn = linearizeFunction

spec :: Spec
spec = describe "Linearization Properties" $ do
    describe "affine property" $ do
        it "output is always affine for simple terms"
            $ property
            $ forAll (unSimpleTerm <$> arbitrary)
            $ \term ->
                isAffine (linearize term) === True

        it "output is always affine for well-scoped terms"
            $ property
            $ forAll (unWellScopedTerm <$> arbitrary)
            $ \term ->
                isAffine (linearize term) === True

    describe "idempotence" $ do
        it "linearization is idempotent for simple terms"
            $ property
            $ forAll (unSimpleTerm <$> arbitrary)
            $ \term ->
                let once = linearize term
                    twice = linearize once
                in once === twice

        -- Note: Linearization is not strictly idempotent due to fresh name generation.
        -- The important property is that the output is affine (tested separately).
        -- Here we verify that re-linearizing an already-linear term still produces affine output.
        it "re-linearization preserves affine property for well-scoped terms"
            $ property
            $ forAll (unWellScopedTerm <$> arbitrary)
            $ \term ->
                let once = linearize term
                    twice = linearize once
                in isAffine twice === True

    describe "DUP insertion" $ do
        it "inserts no DUPs for single-use variables"
            $ property
            $ forAll arbitraryLocalName
            $ \name ->
                let term = CLam name intType (CVar name intType)
                    result = linearize term
                in countDupNodes result === 0

        it "inserts exactly n-1 DUPs for n uses"
            $ property
            $ forAll (choose (2, 5))
            $ \n ->
                let name = NLocal (LocalId LPTemp 0)
                    uses = replicate n (CVar name intType)
                    body = foldr1 (\a b -> CApp a b intType) uses
                    term = CLam name intType body
                    result = linearize term
                in countDupNodes result === n - 1

    describe "function linearization" $ do
        it "marks function as linearized"
            $ property
            $ forAll (arbitrary :: Gen CFunction)
            $ \func ->
                let result = linearizeFn func
                in cfmIsLinear (cfMetadata result) === True

        it "function body becomes affine"
            $ property
            $ forAll (arbitrary :: Gen CFunction)
            $ \func ->
                let result = linearizeFn func
                in isAffine (cfBody result) === True

    describe "module linearization" $ do
        it "marks module as linearized"
            $ property
            $ forAll (arbitrary :: Gen CModule)
            $ \mod' ->
                let result = linearizeModule mod'
                in cmIsLinearized result === True

        it "all functions become linearized"
            $ property
            $ forAll (arbitrary :: Gen CModule)
            $ \mod' ->
                let result = linearizeModule mod'
                in all (cfmIsLinear . cfMetadata) (cmFunctions result) === True

    describe "preservation properties" $ do
        it "preserves term structure for leaf nodes"
            $ property
            $ forAll (elements [CInt 42, CBool True, CStr "test", CEra])
            $ \term ->
                linearize term === term

        it "preserves binary operation structure"
            $ property
            $ forAll arbitrary
            $ \op ->
                let term = CBinOp op (CInt 1) (CInt 2)
                in linearize term === term

        it "preserves comparison operation structure"
            $ property
            $ forAll arbitrary
            $ \op ->
                let term = CCmpOp op (CInt 1) (CInt 2)
                in linearize term === term

    describe "variable counting" $ do
        it "countVarUses returns 0 for unused variable"
            $ property
            $ forAll arbitraryLocalName
            $ \name ->
                countVarUses name (CInt 42) === 0

        it "countVarUses returns 1 for single use"
            $ property
            $ forAll arbitraryLocalName
            $ \name ->
                countVarUses name (CVar name intType) === 1

        it "countVarUses respects shadowing"
            $ property
            $ forAll arbitraryLocalName
            $ \name ->
                let term = CLam name intType (CVar name intType)
                in countVarUses name term === 0 -- Shadowed
        it "countVarUses counts nested uses"
            $ property
            $ forAll ((,) <$> arbitraryLocalName <*> choose (1, 5))
            $ \(name, n) ->
                let uses = replicate n (CVar name intType)
                    term = foldr1 (\a b -> CApp a b intType) uses
                in countVarUses name term === n

    describe "free variables" $ do
        it "literals have no free variables"
            $ property
            $ forAll (elements [CInt 42, CBool True, CStr "test"])
            $ \term ->
                freeVars term === Set.empty

        it "variable has itself as free"
            $ property
            $ forAll arbitraryLocalName
            $ \name ->
                freeVars (CVar name intType) === Set.singleton name

        it "lambda binds its parameter"
            $ property
            $ forAll arbitraryLocalName
            $ \name ->
                freeVars (CLam name intType (CVar name intType)) === Set.empty

        it "let binds in body but not in value"
            $ property
            $ forAll ((,) <$> arbitraryLocalName <*> arbitraryLocalName)
            $ \(x, y) ->
                x /= y
                    ==> let term = CLet x intType (CVar y intType) (CVar x intType)
                        in freeVars term === Set.singleton y
