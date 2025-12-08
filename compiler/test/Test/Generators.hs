{-# LANGUAGE FlexibleInstances #-}

{- | QuickCheck generators for Soma compiler types.

These generators produce well-formed values suitable for property testing.
Key considerations:
  - Generated terms should be well-scoped (no unbound variables)
  - Generated types should be well-kinded
  - Size parameters control term depth to avoid explosion
-}
module Test.Generators (
    -- * Name generators
    arbitraryName,
    arbitraryLocalName,
    arbitraryUserName,

    -- * Type generators
    arbitraryType,
    arbitraryPrimitiveType,
    arbitraryFunctionType,

    -- * Circuit IR generators
    arbitraryCTerm,
    genWellScopedTerm,
    genSimpleTerm,

    -- * Newtypes for specialized generation
    WellScopedTerm (..),
    SimpleTerm (..),
    ValidType (..),
) where

import Circuit.Ir
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Project.Name
import Project.Unique (Unique (..))
import Test.QuickCheck
import Typing.Types

-- ============================================================================
-- Name Generators
-- ============================================================================

-- | Generate a local variable name
arbitraryLocalName :: Gen Name
arbitraryLocalName = do
    prefix <- elements [LPTemp, LPParam, LPReg, LPPatternVar]
    idx <- choose (0, 1000)
    pure $ NLocal (LocalId prefix idx)

-- | Generate a user-defined name
arbitraryUserName :: Gen Name
arbitraryUserName = do
    idx <- choose (0, 1000)
    name <- elements ["x", "y", "z", "foo", "bar", "baz", "f", "g", "h"]
    pure $ NUser (Unique idx "test" name)

-- | Generate any kind of name
arbitraryName :: Gen Name
arbitraryName =
    frequency
        [ (3, arbitraryLocalName)
        , (1, arbitraryUserName)
        ]

instance Arbitrary Name where
    arbitrary = arbitraryName
    shrink (NLocal (LocalId prefix idx))
        | idx > 0 = [NLocal (LocalId prefix (idx - 1))]
    shrink _ = []

-- ============================================================================
-- Type Generators
-- ============================================================================

-- | Generate a primitive type
arbitraryPrimitiveType :: Gen Type
arbitraryPrimitiveType =
    elements
        [ intType
        , boolType
        , strType
        , unitType
        , byteType
        ]

-- | Generate a function type with given argument and return types
arbitraryFunctionType :: Gen Type -> Gen Type -> Gen Type
arbitraryFunctionType genArg genRet = TArrow <$> genArg <*> genRet

-- | Generate a type of bounded depth
arbitraryType :: Gen Type
arbitraryType = sized genType
  where
    genType :: Int -> Gen Type
    genType 0 = arbitraryPrimitiveType
    genType n =
        frequency
            [ (4, arbitraryPrimitiveType)
            , (2, TArrow <$> genType (n `div` 2) <*> genType (n `div` 2))
            , (1, arrayType <$> genType (n - 1))
            ]

instance Arbitrary Type where
    arbitrary = arbitraryType
    shrink (TArrow a b) = [a, b] ++ [TArrow a' b' | (a', b') <- shrink (a, b)]
    shrink (TApp a b) = [a, b]
    shrink _ = []

-- | Newtype for valid (well-kinded) types
newtype ValidType = ValidType {unValidType :: Type}
    deriving (Show, Eq)

instance Arbitrary ValidType where
    arbitrary = ValidType <$> arbitraryType

-- ============================================================================
-- Circuit IR Term Generators
-- ============================================================================

-- | Generate a binary operation
instance Arbitrary BinOp where
    arbitrary = elements [OpAdd, OpSub, OpMul, OpDiv, OpMod, OpAnd, OpOr]

-- | Generate a comparison operation
instance Arbitrary CmpOp where
    arbitrary = elements [OpEq, OpNe, OpLt, OpLe, OpGt, OpGe]

-- | Generate a unary operation
instance Arbitrary UnaryOp where
    arbitrary = elements [OpNot, OpNeg]

-- | Generate a simple leaf term (no recursion)
genLeafTerm :: Gen CTerm
genLeafTerm =
    oneof
        [ CInt <$> arbitrary
        , CBool <$> arbitrary
        , CStr <$> elements ["", "hello", "test", "foo"]
        , pure CEra
        ]

-- | Generate a simple term (for quick tests)
genSimpleTerm :: Gen CTerm
genSimpleTerm = sized go
  where
    go :: Int -> Gen CTerm
    go 0 = genLeafTerm
    go n =
        frequency
            [ (3, genLeafTerm)
            , (1, CBinOp <$> arbitrary <*> go (n `div` 2) <*> go (n `div` 2))
            , (1, CCmpOp <$> arbitrary <*> go (n `div` 2) <*> go (n `div` 2))
            , (1, CUnaryOp <$> arbitrary <*> go (n - 1))
            ]

-- | Newtype for simple terms (no bindings, good for basic property tests)
newtype SimpleTerm = SimpleTerm {unSimpleTerm :: CTerm}
    deriving (Show, Eq)

instance Arbitrary SimpleTerm where
    arbitrary = SimpleTerm <$> genSimpleTerm
    shrink (SimpleTerm t) = SimpleTerm <$> shrinkSimpleTerm t

shrinkSimpleTerm :: CTerm -> [CTerm]
shrinkSimpleTerm (CBinOp _ a b) = [a, b]
shrinkSimpleTerm (CCmpOp _ a b) = [a, b]
shrinkSimpleTerm (CUnaryOp _ a) = [a]
shrinkSimpleTerm _ = []

-- | Scope context for well-scoped term generation
type Scope = Map Name Type

-- | Generate a well-scoped term where all variables are bound
genWellScopedTerm :: Scope -> Int -> Gen CTerm
genWellScopedTerm scope 0 = genWellScopedLeaf scope
genWellScopedTerm scope n =
    frequency
        $ [ (3, genWellScopedLeaf scope)
          , (2, genLambda scope n)
          , (2, genLet scope n)
          , (1, genApp scope n)
          , (1, genBinOp scope n)
          , (1, genCmpOp scope n)
          ]
            ++ if Map.null scope
                then []
                else
                    [(2, genVar scope)]

genWellScopedLeaf :: Scope -> Gen CTerm
genWellScopedLeaf scope
    | Map.null scope = genLeafTerm
    | otherwise =
        frequency
            [ (2, genLeafTerm)
            , (3, genVar scope)
            ]

genVar :: Scope -> Gen CTerm
genVar scope = do
    let vars = Map.toList scope
    (name, ty) <- elements vars
    pure $ CVar name ty

genLambda :: Scope -> Int -> Gen CTerm
genLambda scope n = do
    paramName <- arbitraryLocalName
    paramTy <- arbitraryPrimitiveType
    let scope' = Map.insert paramName paramTy scope
    body <- genWellScopedTerm scope' (n - 1)
    pure $ CLam paramName paramTy body

genLet :: Scope -> Int -> Gen CTerm
genLet scope n = do
    bindName <- arbitraryLocalName
    bindTy <- arbitraryPrimitiveType
    val <- genWellScopedTerm scope (n `div` 2)
    let scope' = Map.insert bindName bindTy scope
    body <- genWellScopedTerm scope' (n `div` 2)
    pure $ CLet bindName bindTy val body

genApp :: Scope -> Int -> Gen CTerm
genApp scope n = do
    argTy <- arbitraryPrimitiveType
    retTy <- arbitraryPrimitiveType
    fun <- genWellScopedTerm scope (n `div` 2)
    arg <- genWellScopedTerm scope (n `div` 2)
    pure $ CApp fun arg retTy

genBinOp :: Scope -> Int -> Gen CTerm
genBinOp scope n = do
    op <- arbitrary
    a <- genWellScopedTerm scope (n `div` 2)
    b <- genWellScopedTerm scope (n `div` 2)
    pure $ CBinOp op a b

genCmpOp :: Scope -> Int -> Gen CTerm
genCmpOp scope n = do
    op <- arbitrary
    a <- genWellScopedTerm scope (n `div` 2)
    b <- genWellScopedTerm scope (n `div` 2)
    pure $ CCmpOp op a b

-- | Newtype for well-scoped terms (all variables bound)
newtype WellScopedTerm = WellScopedTerm {unWellScopedTerm :: CTerm}
    deriving (Show, Eq)

instance Arbitrary WellScopedTerm where
    arbitrary = WellScopedTerm <$> sized (genWellScopedTerm Map.empty)
    shrink (WellScopedTerm t) = WellScopedTerm <$> shrinkWellScoped t

-- | Shrink a well-scoped term while preserving well-scopedness
shrinkWellScoped :: CTerm -> [CTerm]
shrinkWellScoped term = case term of
    -- Shrink to children that are self-contained
    CLam _ _ body -> [body | isClosedTerm body]
    CLet _ _ val body ->
        [val | isClosedTerm val]
            ++ [body | isClosedTerm body]
    CApp f x _ -> [f, x]
    CBinOp _ a b -> [a, b]
    CCmpOp _ a b -> [a, b]
    CUnaryOp _ a -> [a]
    CDup _ _ _ val body -> [val] ++ [body | isClosedTerm body]
    CErase val body -> [val, body]
    CTag _ fields _ -> fields
    CCase scrut _ _ _ -> [scrut]
    _ -> []

-- | Check if a term has no free variables
isClosedTerm :: CTerm -> Bool
isClosedTerm term = null (freeVars term)

-- | Generate an arbitrary Circuit term (may have free variables)
arbitraryCTerm :: Gen CTerm
arbitraryCTerm = sized go
  where
    go :: Int -> Gen CTerm
    go 0 =
        oneof
            [ CInt <$> arbitrary
            , CBool <$> arbitrary
            , CVar <$> arbitraryLocalName <*> arbitraryPrimitiveType
            ]
    go n =
        frequency
            [ (2, CInt <$> arbitrary)
            , (2, CBool <$> arbitrary)
            , (2, CVar <$> arbitraryLocalName <*> arbitraryPrimitiveType)
            , (1, CLam <$> arbitraryLocalName <*> arbitraryPrimitiveType <*> go (n - 1))
            , (1, CApp <$> go (n `div` 2) <*> go (n `div` 2) <*> arbitraryPrimitiveType)
            ,
                ( 1
                , CLet
                    <$> arbitraryLocalName
                    <*> arbitraryPrimitiveType
                    <*> go (n `div` 2)
                    <*> go (n `div` 2)
                )
            , (1, CBinOp <$> arbitrary <*> go (n `div` 2) <*> go (n `div` 2))
            , (1, CCmpOp <$> arbitrary <*> go (n `div` 2) <*> go (n `div` 2))
            ]

instance Arbitrary CTerm where
    arbitrary = arbitraryCTerm
    shrink = shrinkCTerm

shrinkCTerm :: CTerm -> [CTerm]
shrinkCTerm term = case term of
    CInt n -> CInt <$> shrink n
    CLam _ _ body -> [body]
    CApp f x _ -> [f, x]
    CLet _ _ val body -> [val, body]
    CBinOp _ a b -> [a, b]
    CCmpOp _ a b -> [a, b]
    CUnaryOp _ a -> [a]
    CDup _ _ _ val body -> [val, body]
    CErase val body -> [val, body]
    CSup _ a b _ -> [a, b]
    CTag _ fields _ -> fields
    CCase scrut arms mdef _ ->
        scrut : [body | (_, _, body) <- arms] ++ maybe [] pure mdef
    CProject e _ _ -> [e]
    CClosureGetEnv e _ _ -> [e]
    CFork _ _ comp cont -> [comp, cont]
    _ -> []

-- ============================================================================
-- Circuit Function Generators
-- ============================================================================

instance Arbitrary CFunction where
    arbitrary = do
        name <- arbitraryUserName
        numParams <- choose (0, 3)
        params <- vectorOf numParams $ (,) <$> arbitraryLocalName <*> arbitraryPrimitiveType
        retTy <- arbitraryPrimitiveType
        let scope = Map.fromList params
        body <- sized $ \n -> genWellScopedTerm scope (min n 5)
        pure $ mkFunction name params retTy body

-- ============================================================================
-- Module Generators
-- ============================================================================

instance Arbitrary CModule where
    arbitrary = do
        numFuncs <- choose (1, 5)
        funcs <- vectorOf numFuncs arbitrary
        pure
            $ CModule
                { cmName = "test_module"
                , cmFunctions = funcs
                , cmTypes = []
                , cmIsLinearized = False
                , cmExternalRefs = []
                }
