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
import Typing.Types (Type)

-- | Simplify a complete module
simplifyModule :: CModule -> CModule
simplifyModule m =
    m{cmFunctions = map simplifyFunction (cmFunctions m)}

-- | Simplify a function
simplifyFunction :: CFunction -> CFunction
simplifyFunction f =
    f{cfBody = simplifyTerm (cfBody f)}

-- | Simplify a term (main entry point)
simplifyTerm :: CTerm -> CTerm
simplifyTerm = go
  where
    go term = case term of
        -- Let simplifications
        CLet name ty val body ->
            let val' = go val
                body' = go body
                uses = countVarUses name body'
            in simplifyLet name ty val' body' uses
        -- Recursively simplify subterms
        CLam n ty body -> CLam n ty (go body)
        CApp f x ty -> CApp (go f) (go x) ty
        CSup l a b ty -> CSup l (go a) (go b) ty
        CDup n ty l val body -> CDup n ty l (go val) (go body)
        CTag tag fields ty -> CTag tag (map go fields) ty
        CCase scrut arms mdef ty ->
            let scrut' = go scrut
                arms' = [(t, fts, go b) | (t, fts, b) <- arms]
                mdef' = fmap go mdef
            in simplifyCase scrut' arms' mdef' ty
        CBinOp op a b -> CBinOp op (go a) (go b)
        CCmpOp op a b -> CCmpOp op (go a) (go b)
        CUnaryOp op a -> CUnaryOp op (go a)
        -- Closures: no simplification needed (already simple)
        CClosure{} -> term
        -- Closure env access: simplify the closure term
        CClosureGetEnv closure idx ty -> CClosureGetEnv (go closure) idx ty
        -- Field projection: simplify the expression
        CProject expr idx ty -> CProject (go expr) idx ty
        -- Fork/Join: recursively simplify
        CFork n ty comp body -> CFork n ty (go comp) (go body)
        CJoin _ _ -> term
        -- Base cases: no simplification
        CVar _ _ -> term
        CDp0 _ _ -> term
        CDp1 _ _ -> term
        CEra -> term
        CRef _ _ -> term
        CInt _ -> term
        CBool _ -> term
        CStr _ -> term
        CPanic _ _ -> term

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

{- | Check if a value is simple enough to inline unconditionally
Simple values don't create work when duplicated
-}
isSimpleValue :: CTerm -> Bool
isSimpleValue = \case
    CVar _ _ -> True
    CInt _ -> True
    CBool _ -> True
    CStr _ -> True
    CRef _ _ -> True
    CEra -> True
    CDp0 _ _ -> True
    CDp1 _ _ -> True
    _ -> False

-- | Check if a term is a variable or projection (can be substituted into closures)
isVarOrProjection :: CTerm -> Bool
isVarOrProjection = \case
    CVar _ _ -> True
    CDp0 _ _ -> True
    CDp1 _ _ -> True
    _ -> False

-- | Check if a variable is captured by any closure in a term
isCapturedByClosure :: Name -> CTerm -> Bool
isCapturedByClosure target = go
  where
    go (CClosure _ capturedVars _) = target `elem` map fst capturedVars
    go (CVar _ _) = False
    go (CLam _ _ body) = go body
    go (CApp f x _) = go f || go x
    go (CLet _ _ val body) = go val || go body
    go (CSup _ a b _) = go a || go b
    go (CDup _ _ _ val body) = go val || go body
    go (CDp0 _ _) = False
    go (CDp1 _ _) = False
    go CEra = False
    go (CRef _ _) = False
    go (CInt _) = False
    go (CBool _) = False
    go (CStr _) = False
    go (CTag _ fields _) = any go fields
    go (CCase scrut arms mdef _) = go scrut || any (\(_, _, b) -> go b) arms || maybe False go mdef
    go (CBinOp _ a b) = go a || go b
    go (CCmpOp _ a b) = go a || go b
    go (CUnaryOp _ a) = go a
    go (CClosureGetEnv closure _ _) = go closure
    go (CProject expr _ _) = go expr
    go (CPanic _ _) = False
    go (CFork _ _ comp body) = go comp || go body
    go (CJoin _ _) = False

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

-- | Substitute a variable with a term
substitute :: Name -> CTerm -> CTerm -> CTerm
substitute target replacement = go
  where
    go (CVar n ty)
        | n == target = replacement
        | otherwise = CVar n ty
    go (CLam n ty body)
        | n == target = CLam n ty body -- Shadowed
        | otherwise = CLam n ty (go body)
    go (CApp f x ty) = CApp (go f) (go x) ty
    go (CLet n ty val body)
        | n == target = CLet n ty (go val) body -- Shadowed in body
        | otherwise = CLet n ty (go val) (go body)
    go (CSup l a b ty) = CSup l (go a) (go b) ty
    go (CDup n ty l val body)
        | n == target = CDup n ty l (go val) body -- Shadowed
        | otherwise = CDup n ty l (go val) (go body)
    go (CDp0 n ty)
        | n == target = case replacement of
            CDp0 m mTy -> CDp0 m mTy
            CDp1 m mTy -> CDp1 m mTy
            _ -> replacement
        | otherwise = CDp0 n ty
    go (CDp1 n ty)
        | n == target = case replacement of
            CDp0 m mTy -> CDp0 m mTy
            CDp1 m mTy -> CDp1 m mTy
            _ -> replacement
        | otherwise = CDp1 n ty
    go CEra = CEra
    go (CRef n ty) = CRef n ty
    go (CInt i) = CInt i
    go (CBool b) = CBool b
    go (CStr s) = CStr s
    go (CTag tag fields ty) = CTag tag (map go fields) ty
    go (CCase scrut arms mdef ty) =
        CCase
            (go scrut)
            [(tag, fts, if target `elem` map fst fts then body else go body) | (tag, fts, body) <- arms]
            (go <$> mdef)
            ty
    go (CBinOp op a b) = CBinOp op (go a) (go b)
    go (CCmpOp op a b) = CCmpOp op (go a) (go b)
    go (CUnaryOp op a) = CUnaryOp op (go a)
    go (CClosure liftedName capturedVars closureTy) =
        -- Substitute in captured vars list
        let capturedVars' = [(if n == target then getReplacementName else n, t) | (n, t) <- capturedVars]
        in CClosure liftedName capturedVars' closureTy
      where
        getReplacementName = case replacement of
            CVar repName _ -> repName
            CDp0 repName _ -> repName ++ ".0"
            CDp1 repName _ -> repName ++ ".1"
            _ -> target
    go (CClosureGetEnv closure idx ty) = CClosureGetEnv (go closure) idx ty
    go (CProject expr idx ty) = CProject (go expr) idx ty
    go (CPanic msg ty) = CPanic msg ty
    go (CFork n ty comp body) = CFork n ty (go comp) (go body)
    go (CJoin n ty) = CJoin n ty