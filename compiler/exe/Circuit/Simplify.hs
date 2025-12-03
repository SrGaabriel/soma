{-# LANGUAGE LambdaCase #-}

{- | Simplification pass for Circuit IR.

This pass performs local simplifications on the Circuit IR to reduce
unnecessary complexity before linearization or code generation.

Simplifications performed:
1. Let-var elimination: `let x = y in x` => `y`
2. Let inlining: `let x = v in body` where x used once => body[x := v]
3. Identity case elimination: `case x of { <t, y> -> y }` for single-field
4. Dead let elimination: `let x = v in body` where x unused => body
5. Constant folding: `1 + 2` => `3`
6. Identity operations: `x + 0` => `x`, `x * 1` => `x`
7. Algebraic simplifications: `x - x` => `0`, `x * 0` => `0`
8. Boolean simplifications: `not (not x)` => `x`, `true && x` => `x`
9. Comparison simplifications: `x == x` => `true`

These simplifications reduce the number of DUP nodes needed after linearization
and produce cleaner code overall.
-}
module Circuit.Simplify (
    simplifyModule,
    simplifyFunction,
    simplifyTerm,
) where

import Circuit.Ir
import qualified Data.Bits
import Data.Monoid (Any (..))
import Typing.Types (Type)

-- | Simplify a complete module
simplifyModule :: CModule -> CModule
simplifyModule m =
    m{cmFunctions = map simplifyFunction (cmFunctions m)}

-- | Simplify a function
simplifyFunction :: CFunction -> CFunction
simplifyFunction f =
    f{cfBody = simplifyTerm (cfBody f)}

{- | Simplify a term (main entry point).

Uses bottom-up traversal with special handling for CLet, CCase,
and arithmetic/logical operations which have custom simplification rules.
-}
simplifyTerm :: CTerm -> CTerm
simplifyTerm = go
  where
    go term = case term of
        -- Let simplifications need special handling
        CLet name ty val body ->
            let val' = go val
                body' = go body
                uses = countVarUses name body'
            in simplifyLet name ty val' body' uses
        -- Case simplifications need special handling
        CCase scrut arms mdef ty ->
            let scrut' = go scrut
                arms' = [(t, fts, go b) | (t, fts, b) <- arms]
                mdef' = fmap go mdef
            in simplifyCase scrut' arms' mdef' ty
        -- Binary operations: constant folding and algebraic simplifications
        CBinOp op a b ->
            let a' = go a
                b' = go b
            in simplifyBinOp op a' b'
        -- Comparison operations: constant folding and identity checks
        CCmpOp op a b ->
            let a' = go a
                b' = go b
            in simplifyCmpOp op a' b'
        -- Unary operations: constant folding and double-negation
        CUnaryOp op a ->
            let a' = go a
            in simplifyUnaryOp op a'
        -- All other terms: just recurse into children
        _ -> mapChildren go term

-- ============================================================================
-- Binary Operation Simplifications
-- ============================================================================

{- | Simplify binary operations.

Performs:
1. Constant folding: CInt a `op` CInt b => CInt result
2. Identity operations: x + 0 => x, x * 1 => x, x - 0 => x
3. Zero operations: x * 0 => 0, 0 / x => 0 (when x != 0)
4. Self operations: x - x => 0, x / x => 1 (when x is a variable)
5. Bitwise identities: x & 0 => 0, x | 0 => x, x ^ 0 => x
-}
simplifyBinOp :: BinOp -> CTerm -> CTerm -> CTerm
simplifyBinOp op a b = case (op, a, b) of
    -- Constant folding for arithmetic
    (OpAdd, CInt x, CInt y) -> CInt (x + y)
    (OpSub, CInt x, CInt y) -> CInt (x - y)
    (OpMul, CInt x, CInt y) -> CInt (x * y)
    (OpDiv, CInt x, CInt y) | y /= 0 -> CInt (x `div` y)
    (OpMod, CInt x, CInt y) | y /= 0 -> CInt (x `mod` y)
    -- Constant folding for bitwise operations
    (OpAnd, CInt x, CInt y) -> CInt (x .&. y)
    (OpOr, CInt x, CInt y) -> CInt (x .|. y)
    (OpXor, CInt x, CInt y) -> CInt (x `xor` y)
    (OpShl, CInt x, CInt y) | y >= 0 && y < 64 -> CInt (x `shiftL` y)
    (OpShr, CInt x, CInt y) | y >= 0 && y < 64 -> CInt (x `shiftR` y)
    -- Addition identities: x + 0 = 0 + x = x
    (OpAdd, x, CInt 0) -> x
    (OpAdd, CInt 0, x) -> x
    -- Subtraction identities: x - 0 = x
    (OpSub, x, CInt 0) -> x
    -- x - x = 0 (only for simple variables to avoid duplicating effects)
    (OpSub, CVar n1 _, CVar n2 _) | n1 == n2 -> CInt 0
    -- Multiplication identities: x * 1 = 1 * x = x, x * 0 = 0 * x = 0
    (OpMul, x, CInt 1) -> x
    (OpMul, CInt 1, x) -> x
    (OpMul, _, CInt 0) -> CInt 0
    (OpMul, CInt 0, _) -> CInt 0
    -- x * 2 = x + x (but we don't do this as it may increase DUPs)
    -- x * (-1) = -x
    (OpMul, x, CInt (-1)) -> CUnaryOp OpNeg x
    (OpMul, CInt (-1), x) -> CUnaryOp OpNeg x
    -- Division identities: x / 1 = x, 0 / x = 0 (assuming x != 0)
    (OpDiv, x, CInt 1) -> x
    (OpDiv, CInt 0, _) -> CInt 0
    -- x / x = 1 (only for simple variables)
    (OpDiv, CVar n1 _, CVar n2 _) | n1 == n2 -> CInt 1
    -- Modulo identities: x % 1 = 0, 0 % x = 0
    (OpMod, _, CInt 1) -> CInt 0
    (OpMod, CInt 0, _) -> CInt 0
    -- x % x = 0 (only for simple variables)
    (OpMod, CVar n1 _, CVar n2 _) | n1 == n2 -> CInt 0
    -- Bitwise AND identities: x & 0 = 0, x & -1 (all 1s) = x
    (OpAnd, _, CInt 0) -> CInt 0
    (OpAnd, CInt 0, _) -> CInt 0
    (OpAnd, x, CInt (-1)) -> x
    (OpAnd, CInt (-1), x) -> x
    -- x & x = x (only for simple variables)
    (OpAnd, CVar n1 ty, CVar n2 _) | n1 == n2 -> CVar n1 ty
    -- Bitwise OR identities: x | 0 = x, x | -1 = -1
    (OpOr, x, CInt 0) -> x
    (OpOr, CInt 0, x) -> x
    (OpOr, _, CInt (-1)) -> CInt (-1)
    (OpOr, CInt (-1), _) -> CInt (-1)
    -- x | x = x (only for simple variables)
    (OpOr, CVar n1 ty, CVar n2 _) | n1 == n2 -> CVar n1 ty
    -- Bitwise XOR identities: x ^ 0 = x
    (OpXor, x, CInt 0) -> x
    (OpXor, CInt 0, x) -> x
    -- x ^ x = 0 (only for simple variables)
    (OpXor, CVar n1 _, CVar n2 _) | n1 == n2 -> CInt 0
    -- Shift identities: x << 0 = x, x >> 0 = x
    (OpShl, x, CInt 0) -> x
    (OpShr, x, CInt 0) -> x
    -- 0 << n = 0, 0 >> n = 0
    (OpShl, CInt 0, _) -> CInt 0
    (OpShr, CInt 0, _) -> CInt 0
    -- No simplification possible
    _ -> CBinOp op a b
  where
    -- Import Data.Bits operations
    (.&.) = (Data.Bits..&.)
    (.|.) = (Data.Bits..|.)
    xor = Data.Bits.xor
    shiftL = Data.Bits.shiftL
    shiftR = Data.Bits.shiftR

-- ============================================================================
-- Comparison Operation Simplifications
-- ============================================================================

{- | Simplify comparison operations.

Performs:
1. Constant folding: CInt a `cmp` CInt b => CBool result
2. Identity comparisons: x == x => true, x != x => false (for simple vars)
3. Boolean constant comparisons
-}
simplifyCmpOp :: CmpOp -> CTerm -> CTerm -> CTerm
simplifyCmpOp op a b = case (op, a, b) of
    -- Constant folding
    (OpEq, CInt x, CInt y) -> CBool (x == y)
    (OpNe, CInt x, CInt y) -> CBool (x /= y)
    (OpLt, CInt x, CInt y) -> CBool (x < y)
    (OpLe, CInt x, CInt y) -> CBool (x <= y)
    (OpGt, CInt x, CInt y) -> CBool (x > y)
    (OpGe, CInt x, CInt y) -> CBool (x >= y)
    -- Boolean constant folding
    (OpEq, CBool x, CBool y) -> CBool (x == y)
    (OpNe, CBool x, CBool y) -> CBool (x /= y)
    -- Self-comparison (only for simple variables to avoid duplicating effects)
    (OpEq, CVar n1 _, CVar n2 _) | n1 == n2 -> CBool True
    (OpNe, CVar n1 _, CVar n2 _) | n1 == n2 -> CBool False
    (OpLe, CVar n1 _, CVar n2 _) | n1 == n2 -> CBool True -- x <= x is always true
    (OpGe, CVar n1 _, CVar n2 _) | n1 == n2 -> CBool True -- x >= x is always true
    (OpLt, CVar n1 _, CVar n2 _) | n1 == n2 -> CBool False -- x < x is always false
    (OpGt, CVar n1 _, CVar n2 _) | n1 == n2 -> CBool False -- x > x is always false

    -- No simplification possible
    _ -> CCmpOp op a b

-- ============================================================================
-- Unary Operation Simplifications
-- ============================================================================

{- | Simplify unary operations.

Performs:
1. Constant folding: not true => false, -5 => -5
2. Double negation: not (not x) => x, -(-x) => x
-}
simplifyUnaryOp :: UnaryOp -> CTerm -> CTerm
simplifyUnaryOp op a = case (op, a) of
    -- Constant folding for NOT
    (OpNot, CBool True) -> CBool False
    (OpNot, CBool False) -> CBool True
    -- Constant folding for NEG
    (OpNeg, CInt x) -> CInt (-x)
    -- Double negation elimination: not (not x) => x
    (OpNot, CUnaryOp OpNot x) -> x
    -- Double arithmetic negation: -(-x) => x
    (OpNeg, CUnaryOp OpNeg x) -> x
    -- No simplification possible
    _ -> CUnaryOp op a

-- | Simplify a let binding based on usage
simplifyLet :: Name -> Type -> CTerm -> CTerm -> Int -> CTerm
simplifyLet name ty val body uses
    -- Dead code elimination: unused binding
    | uses == 0 = body
    -- Let-var elimination: `let x = y in x` => `y`
    | CVar n _ <- body, n == name = val
    -- Don't inline literals captured by closures (closures store names, not values)
    | isCapturedByClosure name body, not (isVarOrProjection val) = CLet name ty val body
    -- Inline simple values used once
    | uses == 1, isSimpleValue val = substitute name val body
    -- Inline variables (always safe, no duplication)
    | CVar _ _ <- val = substitute name val body
    -- Otherwise keep the let
    | otherwise = CLet name ty val body

{- | Check if a value is simple enough to inline unconditionally.

Simple values don't create work when duplicated.
-}
isSimpleValue :: CTerm -> Bool
isSimpleValue = \case
    CVar{} -> True
    CInt{} -> True
    CBool{} -> True
    CStr{} -> True
    CRef{} -> True
    CEra -> True
    CDp0{} -> True
    CDp1{} -> True
    _ -> False

-- | Check if a term is a variable or projection (can be substituted into closures)
isVarOrProjection :: CTerm -> Bool
isVarOrProjection = \case
    CVar{} -> True
    CDp0{} -> True
    CDp1{} -> True
    _ -> False

{- | Check if a variable is captured by any closure in a term.

Uses foldChildren with Any monoid for a cleaner implementation.
-}
isCapturedByClosure :: Name -> CTerm -> Bool
isCapturedByClosure target = getAny . go
  where
    go term = case term of
        CClosure _ capturedVars _ -> Any (target `elem` map fst capturedVars)
        _ -> foldChildren go term

-- | Simplify a case expression
simplifyCase :: CTerm -> [(Int, [(Name, Type)], CTerm)] -> Maybe CTerm -> Type -> CTerm
simplifyCase scrut arms mdef ty
    -- Single arm with single field that just returns the field
    -- `case x of { <t, y> -> y }` => project field from x
    | [(_, [(fieldName, fieldTy)], CVar v _)] <- arms
    , Nothing <- mdef
    , v == fieldName =
        -- Replace with direct field projection (field index 0)
        CProject scrut 0 fieldTy
    -- Case on a known tag value
    | CTag tag fields _ <- scrut
    , Just (_, fieldsWithTypes, body) <- lookupArm tag arms =
        -- Inline the matched arm with field substitutions
        substituteFields (zip (map fst fieldsWithTypes) fields) body
    -- Case on a known tag with default
    | CTag tag _ _ <- scrut
    , Nothing <- lookupArm tag arms
    , Just def <- mdef =
        def
    -- Otherwise keep the case
    | otherwise = CCase scrut arms mdef ty
  where
    lookupArm t as = case [(fts, b) | (t', fts, b) <- as, t' == t] of
        [(fts, b)] -> Just (t, fts, b)
        _ -> Nothing

-- | Substitute fields into a body
substituteFields :: [(Name, CTerm)] -> CTerm -> CTerm
substituteFields [] body = body
substituteFields ((n, v) : rest) body =
    substituteFields rest (substitute n v body)

{- | Substitute a variable with a term.

This is binding-aware: substitution stops at binders that shadow the target.
Uses mapChildren for non-binding cases.
-}
substitute :: Name -> CTerm -> CTerm -> CTerm
substitute target replacement = go
  where
    go term = case term of
        -- Variable references: substitute if matches
        CVar n _
            | n == target -> replacement
        CDp0 n _
            | n == target -> case replacement of
                CDp0 m mTy -> CDp0 m mTy
                CDp1 m mTy -> CDp1 m mTy
                _ -> replacement
        CDp1 n _
            | n == target -> case replacement of
                CDp0 m mTy -> CDp0 m mTy
                CDp1 m mTy -> CDp1 m mTy
                _ -> replacement
        -- Binding forms: check for shadowing
        CLam n ty body
            | n == target -> CLam n ty body -- Shadowed
            | otherwise -> CLam n ty (go body)
        CLet n ty val body
            | n == target -> CLet n ty (go val) body -- Shadowed in body
            | otherwise -> CLet n ty (go val) (go body)
        CDup n ty l val body
            | n == target -> CDup n ty l (go val) body -- Shadowed
            | otherwise -> CDup n ty l (go val) (go body)
        CCase scrut arms mdef ty ->
            CCase
                (go scrut)
                [(tag, fts, if target `elem` map fst fts then body else go body) | (tag, fts, body) <- arms]
                (go <$> mdef)
                ty
        -- CClosure: substitute in captured vars list
        CClosure liftedName capturedVars closureTy ->
            let capturedVars' = [(if n == target then getReplacementName else n, t) | (n, t) <- capturedVars]
            in CClosure liftedName capturedVars' closureTy
          where
            getReplacementName = case replacement of
                CVar repName _ -> repName
                CDp0 repName _ -> repName ++ ".0"
                CDp1 repName _ -> repName ++ ".1"
                _ -> target
        -- All other terms: just recurse into children
        _ -> mapChildren go term
