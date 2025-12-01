{-# LANGUAGE LambdaCase #-}

{- | Simplification pass for Circuit IR.

This pass performs local simplifications on the Circuit IR to reduce
unnecessary complexity before linearization or code generation.

Simplifications performed:
1. Let-var elimination: `let x = y in x` => `y`
2. Let inlining: `let x = v in body` where x used once => body[x := v]
3. Identity case elimination: `case x of { <t, y> -> y }` for single-field
4. Dead let elimination: `let x = v in body` where x unused => body

These simplifications reduce the number of DUP nodes needed after linearization
and produce cleaner code overall.
-}
module Circuit.Simplify (
    simplifyModule,
    simplifyFunction,
    simplifyTerm,
) where

import Circuit.Ir
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

Uses bottom-up traversal with special handling for CLet and CCase
which have custom simplification rules.
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
        -- All other terms: just recurse into children
        _ -> mapChildren go term

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
