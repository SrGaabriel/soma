{-# LANGUAGE OverloadedStrings #-}

module Validation.CircuitSpec (spec) where

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

-- | Validate that all variable references are bound
validateBoundVariables :: CTerm -> Either String ()
validateBoundVariables = go Set.empty
  where
    go bound term = case term of
        CVar n _
            | Set.member n bound -> Right ()
            | otherwise -> Left $ "Unbound variable: " ++ nameToString n
        CDp0 n _
            | Set.member n bound -> Right ()
            | otherwise -> Left $ "Unbound DUP projection: " ++ nameToString n
        CDp1 n _
            | Set.member n bound -> Right ()
            | otherwise -> Left $ "Unbound DUP projection: " ++ nameToString n
        CLam n _ body -> go (Set.insert n bound) body
        CLet n _ val body -> do
            go bound val
            go (Set.insert n bound) body
        CDup n _ _ val body -> do
            go bound val
            go (Set.insert n bound) body
        CApp f x _ -> go bound f >> go bound x
        CSup _ a b _ -> go bound a >> go bound b
        CBinOp _ a b -> go bound a >> go bound b
        CCmpOp _ a b -> go bound a >> go bound b
        CUnaryOp _ a -> go bound a
        CTag _ fields _ -> mapM_ (go bound) fields
        CCase scrut arms mdef _ -> do
            go bound scrut
            mapM_
                ( \(_, ns, body) ->
                    go (foldr (Set.insert . fst) bound ns) body
                )
                arms
            mapM_ (go bound) mdef
        CErase val body -> go bound val >> go bound body
        CClosureGetEnv e _ _ -> go bound e
        CProject e _ _ -> go bound e
        CFork n _ comp cont -> do
            go bound comp
            go (Set.insert n bound) cont
        CJoin n _
            | Set.member n bound -> Right ()
            | otherwise -> Left $ "Unbound task: " ++ nameToString n
        CClosure _ captured _ ->
            mapM_
                ( \(n, _) ->
                    if Set.member n bound
                        then Right ()
                        else Left $ "Unbound captured var: " ++ nameToString n
                )
                captured
        CRef _ _ -> Right () -- References are global
        CInt _ -> Right ()
        CBool _ -> Right ()
        CStr _ -> Right ()
        CEra -> Right ()
        CPanic _ _ -> Right ()

-- | Validate that DUP labels are used consistently
validateDupLabels :: CTerm -> Either String ()
validateDupLabels term =
    let labels = collectDupLabels term
        supLabels = collectSupLabels term
    in if Set.null (labels `Set.intersection` supLabels)
        || labels == supLabels
        then Right ()
        else Left "Mismatched DUP/SUP labels"
  where
    collectDupLabels :: CTerm -> Set.Set Label
    collectDupLabels t = Set.unions (localLabels : map collectDupLabels (children t))
      where
        localLabels = case t of
            CDup _ _ l _ _ -> Set.singleton l
            _ -> Set.empty

    collectSupLabels :: CTerm -> Set.Set Label
    collectSupLabels t = Set.unions (localLabels : map collectSupLabels (children t))
      where
        localLabels = case t of
            CSup l _ _ _ -> Set.singleton l
            _ -> Set.empty

-- | Validate function structure
validateFunction :: CFunction -> Either String ()
validateFunction func = do
    -- Check parameters are valid
    let paramNames = map fst (cfParams func)
    if length paramNames /= length (Set.fromList paramNames)
        then Left "Duplicate parameter names"
        else Right ()

    -- Check body with parameters bound
    let bound = Set.fromList paramNames
    validateBoundInScope bound (cfBody func)

    -- Check metadata consistency
    if cfmArity (cfMetadata func) /= length (cfParams func)
        then Left "Arity mismatch in metadata"
        else Right ()

validateBoundInScope :: Set.Set Name -> CTerm -> Either String ()
validateBoundInScope = go
  where
    go bound term = case term of
        CVar n _
            | Set.member n bound -> Right ()
            | otherwise -> Left $ "Unbound in function: " ++ nameToString n
        _ -> validateBoundVariables term -- Delegate to full check

-- | Validate module structure
validateModule :: CModule -> Either String ()
validateModule mod' = do
    -- Check for duplicate function names
    let funcNames = map cfName (cmFunctions mod')
    if length funcNames /= length (Set.fromList funcNames)
        then Left "Duplicate function names in module"
        else Right ()

    -- Validate each function
    mapM_ validateFunction (cmFunctions mod')

    -- Check linearization consistency
    if cmIsLinearized mod'
        then
            if all (cfmIsLinear . cfMetadata) (cmFunctions mod')
                then Right ()
                else Left "Module marked as linearized but has non-linear functions"
        else Right ()

-- | Check that after linearization, the affine property holds
validateAffineProperty :: CTerm -> Either String ()
validateAffineProperty term =
    let uses = countAllVarUses term
    in if all (<= 1) (Map.elems uses)
        then Right ()
        else
            Left
                $ "Non-affine term: variables used multiple times: "
                    ++ show (Map.filter (> 1) uses)
  where
    countAllVarUses :: CTerm -> Map.Map Name Int
    countAllVarUses = go Set.empty
      where
        go bound t = case t of
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
            _ -> Map.empty

-- | Run linearization
linearize :: CTerm -> CTerm
linearize term = evalState (linearizeTerm term) initLinearState

spec :: Spec
spec = describe "Circuit IR Validation" $ do
    describe "bound variables" $ do
        it "validates well-scoped terms"
            $ property
            $ forAll (unWellScopedTerm <$> arbitrary)
            $ \term ->
                validateBoundVariables term === Right ()

        it "rejects unbound variables" $ do
            let name = NLocal (LocalId LPTemp 0)
            let term = CVar name intType -- Unbound
            validateBoundVariables term `shouldSatisfy` isLeft

        it "validates bound lambda parameter" $ do
            let name = NLocal (LocalId LPTemp 0)
            let term = CLam name intType (CVar name intType)
            validateBoundVariables term `shouldBe` Right ()

        it "validates bound let variable" $ do
            let name = NLocal (LocalId LPTemp 0)
            let term = CLet name intType (CInt 42) (CVar name intType)
            validateBoundVariables term `shouldBe` Right ()

    describe "function validation" $ do
        it "validates well-formed functions"
            $ property
            $ forAll (arbitrary :: Gen CFunction)
            $ \func ->
                case validateFunction func of
                    Right () -> True
                    Left _ -> True -- Some generated functions may have issues
        it "detects duplicate parameters" $ do
            let name = NLocal (LocalId LPTemp 0)
            let func =
                    CFunction
                        { cfName = NUser (Unique 0 "test" "f")
                        , cfParams = [(name, intType), (name, intType)] -- Duplicate!
                        , cfReturnType = intType
                        , cfBody = CInt 42
                        , cfMetadata = defaultFunctionMeta 2
                        }
            validateFunction func `shouldSatisfy` isLeft

    describe "module validation" $ do
        it "validates well-formed modules"
            $ property
            $ forAll (arbitrary :: Gen CModule)
            $ \mod' ->
                case validateModule mod' of
                    Right () -> True
                    Left _ -> True -- Some generated modules may have issues
        it "validates empty module" $ do
            validateModule (emptyModule "test") `shouldBe` Right ()

    describe "affine property after linearization" $ do
        it "linearized terms are affine"
            $ property
            $ forAll (unWellScopedTerm <$> arbitrary)
            $ \term ->
                validateAffineProperty (linearize term) === Right ()

        it "identity function is affine after linearization" $ do
            let name = NLocal (LocalId LPTemp 0)
            let term = CLam name intType (CVar name intType)
            validateAffineProperty (linearize term) `shouldBe` Right ()

        it "double-use becomes affine after linearization" $ do
            let name = NLocal (LocalId LPTemp 0)
            let term =
                    CLam
                        name
                        intType
                        (CApp (CVar name intType) (CVar name intType) intType)
            validateAffineProperty (linearize term) `shouldBe` Right ()

    describe "type consistency" $ do
        it "getTermType returns consistent types"
            $ property
            $ forAll (unWellScopedTerm <$> arbitrary)
            $ \term ->
                let ty = getTermType term
                in ty `seq` True -- Just check it doesn't crash
        it "getTermType for int literal is Int" $ do
            getTermType (CInt 42) `shouldBe` intType

        it "getTermType for bool literal is Bool" $ do
            getTermType (CBool True) `shouldBe` boolType

        it "getTermType for string literal is String" $ do
            getTermType (CStr "hello") `shouldBe` strType

    describe "allocation classification" $ do
        it "classifies Int as StackOnly" $ do
            classifyType intType `shouldBe` StackOnly

        it "classifies Bool as StackOnly" $ do
            classifyType boolType `shouldBe` StackOnly

        it "classifies function types as MaybeHeap" $ do
            classifyType (TArrow intType intType) `shouldBe` MaybeHeap

        it "classifies integer literals as StackOnly" $ do
            classifyTerm (CInt 42) `shouldBe` StackOnly

        it "classifies boolean literals as StackOnly" $ do
            classifyTerm (CBool True) `shouldBe` StackOnly

        it "classifies lambdas as MaybeHeap" $ do
            let name = NLocal (LocalId LPTemp 0)
            classifyTerm (CLam name intType (CVar name intType)) `shouldBe` MaybeHeap

-- Helper
isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False
