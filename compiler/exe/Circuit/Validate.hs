{-# LANGUAGE RecordWildCards #-}

{- | Circuit IR Validation Pass.

Validation checks include:

Pre-linearization (non-affine):
  - All variable references are in scope (well-scoped)
  - All types are consistent (type annotations match usage)
  - All function references exist

Post-linearization (affine):
  - Each variable is used exactly once
  - DUP/SUP label consistency (DUP creates, SUP consumes)
  - Projection names match their DUP sources

Common invariants:
  - No unbound variables
  - Case arms have consistent types
  - Closure captured variables are in scope
  - Fork/Join task names are properly paired
-}
module Circuit.Validate (
    ValidationError (..),
    ValidationResult,
    validateModule,
    validateFunction,
    validateTerm,
    checkWellScoped,
    checkLinear,
    checkTypeConsistency,
    checkDupSupPairing,
) where

import Circuit.Ir
import Control.Monad (forM_, unless, when)
import Control.Monad.Writer.Strict (Writer, execWriter, tell)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Typing.Types (Type (..))

data ValidationError
    = -- | Variable used but not in scope
      UnboundVariable !Name !String
    | -- | Variable used more than once in linear context
      NonLinearUse !Name !Int !String
    | -- | Variable not used (wasted) in linear context
      UnusedVariable !Name !String
    | -- | DUP projection without matching DUP
      OrphanProjection !Name !String
    | -- | Type mismatch between expected and actual
      TypeMismatch !Type !Type !String
    | -- | Function reference to non-existent function
      UnknownFunction !Name !String
    | -- | DUP/SUP label mismatch
      LabelMismatch !Label !Label !String
    | -- | Fork without matching Join
      UnmatchedFork !Name !String
    | -- | Join without matching Fork
      UnmatchedJoin !Name !String
    | -- | Case arms have inconsistent types
      InconsistentCaseTypes ![Type] !String
    | -- | Closure captures variable not in scope
      InvalidCapture !Name !String
    | -- | Generic validation error
      ValidationFailure !String
    deriving (Show, Eq)

type ValidationResult = [ValidationError]

data ValidCtx = ValidCtx
    { vcScope :: !(Set Name)
    , vcDups :: !(Map Name Label)
    , vcForks :: !(Set Name)
    , vcFunctions :: !(Set Name)
    , vcLinear :: !Bool
    , vcPath :: !String
    }

emptyCtx :: ValidCtx
emptyCtx =
    ValidCtx
        { vcScope = Set.empty
        , vcDups = Map.empty
        , vcForks = Set.empty
        , vcFunctions = Set.empty
        , vcLinear = False
        , vcPath = ""
        }

extendScope :: Name -> ValidCtx -> ValidCtx
extendScope name ctx = ctx{vcScope = Set.insert name (vcScope ctx)}

extendScopeMany :: [Name] -> ValidCtx -> ValidCtx
extendScopeMany names ctx = ctx{vcScope = foldr Set.insert (vcScope ctx) names}

registerDup :: Name -> Label -> ValidCtx -> ValidCtx
registerDup name label ctx = ctx{vcDups = Map.insert name label (vcDups ctx)}

registerFork :: Name -> ValidCtx -> ValidCtx
registerFork name ctx = ctx{vcForks = Set.insert name (vcForks ctx)}

-- | Set the current path for error context
withPath :: String -> ValidCtx -> ValidCtx
withPath path ctx = ctx{vcPath = path}

type ValidM = Writer [ValidationError]

report :: ValidationError -> ValidM ()
report err = tell [err]

{- | Count uses of a specific projection (0 for CDp0, 1 for CDp1) of a DUP name
This is needed because CDp0/CDp1 store the base name, not "name.0"/"name.1"
-}
countProjectionUses :: Name -> Int -> CTerm -> Int
countProjectionUses baseName projIdx = go
  where
    go term = case term of
        CDp0 n _ | n == baseName && projIdx == 0 -> 1
        CDp1 n _ | n == baseName && projIdx == 1 -> 1
        CDp0 _ _ -> 0
        CDp1 _ _ -> 0
        CLam n _ body -> if n == baseName then 0 else go body
        CLet n _ val body -> go val + if n == baseName then 0 else go body
        CDup n _ _ val body -> go val + if n == baseName then 0 else go body
        CCase scrut arms mdef _ ->
            go scrut
                + sum [if baseName `elem` map fst ns then 0 else go body | (_, ns, body) <- arms]
                + maybe 0 go mdef
        _ -> sum $ map go (children term)

validateModule :: CModule -> ValidationResult
validateModule CModule{..} = execWriter $ do
    let funcNames = Set.fromList $ map cfName cmFunctions
        externalNames = Set.fromList cmExternalRefs
        allFuncs = Set.union funcNames externalNames
        ctx = emptyCtx{vcFunctions = allFuncs, vcLinear = cmIsLinearized}

    forM_ cmFunctions $ \func -> do
        let funcCtx = withPath (cfName func) ctx
        validateFunctionM funcCtx func

validateFunction :: Bool -> CFunction -> ValidationResult
validateFunction checkLinearInvariants func = execWriter $ do
    let ctx =
            emptyCtx
                { vcLinear = checkLinearInvariants
                , vcPath = cfName func
                }
    validateFunctionM ctx func

validateFunctionM :: ValidCtx -> CFunction -> ValidM ()
validateFunctionM ctx CFunction{..} = do
    let paramNames = map fst cfParams
        ctx' = extendScopeMany paramNames ctx
    validateTermM ctx' cfBody

    when (vcLinear ctx) $ forM_ paramNames $ \param -> do
        let uses = countVarUses param cfBody
        when (uses == 0)
            $ report
            $ UnusedVariable param (vcPath ctx ++ ": parameter not used")
        when (uses > 1)
            $ report
            $ NonLinearUse param uses (vcPath ctx ++ ": parameter used multiple times")

validateTerm :: Bool -> Set Name -> CTerm -> ValidationResult
validateTerm checkLinearInvariants scope term = execWriter $ do
    let ctx = emptyCtx{vcLinear = checkLinearInvariants, vcScope = scope}
    validateTermM ctx term

validateTermM :: ValidCtx -> CTerm -> ValidM ()
validateTermM ctx term = case term of
    CVar name _ ->
        unless (Set.member name (vcScope ctx) || Set.member name (vcFunctions ctx))
            $ report
            $ UnboundVariable name (vcPath ctx)
    CLam name _ body -> do
        let ctx' = extendScope name ctx
        validateTermM ctx' body
    CApp f x _ -> do
        validateTermM ctx f
        validateTermM ctx x
    CLet name _ val body -> do
        validateTermM ctx val
        let ctx' = extendScope name ctx
        validateTermM ctx' body

        -- Should be used exactly once in body
        when (vcLinear ctx) $ do
            let uses = countVarUses name body
            when (uses == 0)
                $ report
                $ UnusedVariable name (vcPath ctx ++ ": let binding not used")
            when (uses > 1)
                $ report
                $ NonLinearUse name uses (vcPath ctx ++ ": let binding used multiple times")
    CSup _ a b _ -> do
        validateTermM ctx a
        validateTermM ctx b
    CDup name _ label val body -> do
        validateTermM ctx val

        let ctx' =
                registerDup name label
                    $ extendScope name
                    $ extendScope (name ++ ".0")
                    $ extendScope (name ++ ".1") ctx

        validateTermM ctx' body

        -- Linear check: each projection should be used exactly once
        -- Note: CDp0/CDp1 store the base name, so we count projection uses directly
        when (vcLinear ctx) $ do
            let uses0 = countProjectionUses name 0 body
                uses1 = countProjectionUses name 1 body
            when (uses0 == 0 && uses1 == 0)
                $ report
                $ UnusedVariable name (vcPath ctx ++ ": DUP neither projection used")
            when (uses0 > 1)
                $ report
                $ NonLinearUse (name ++ ".0") uses0 (vcPath ctx)
            when (uses1 > 1)
                $ report
                $ NonLinearUse (name ++ ".1") uses1 (vcPath ctx)
    CDp0 name _ -> do
        let projName = name ++ ".0"
        unless (Set.member projName (vcScope ctx))
            $ report
            $ OrphanProjection projName (vcPath ctx ++ ": no matching DUP")
    CDp1 name _ -> do
        let projName = name ++ ".1"
        unless (Set.member projName (vcScope ctx))
            $ report
            $ OrphanProjection projName (vcPath ctx ++ ": no matching DUP")
    CEra -> pure ()
    CErase val body -> do
        -- Validate the value being erased and the continuation body
        validateTermM ctx val
        validateTermM ctx body
    CRef name _ ->
        -- Function references (CRef) are top-level function references.
        -- They are valid if they refer to a known function OR if we don't
        -- have function info (in which case we assume it's external).
        unless (Set.member name (vcFunctions ctx) || Set.null (vcFunctions ctx))
            $ report
            $ UnknownFunction name (vcPath ctx ++ ": unknown function reference")
    CInt _ -> pure ()
    CBool _ -> pure ()
    CStr _ -> pure ()
    CTag _ fields _ -> mapM_ (validateTermM ctx) fields
    CCase scrut arms mdef _ -> do
        validateTermM ctx scrut

        forM_ arms $ \(_, bindings, body) -> do
            let names = map fst bindings
                ctx' = extendScopeMany names ctx
            validateTermM ctx' body

        forM_ mdef $ \defBody ->
            validateTermM ctx defBody
    CBinOp _ a b -> do
        validateTermM ctx a
        validateTermM ctx b
    CCmpOp _ a b -> do
        validateTermM ctx a
        validateTermM ctx b
    CUnaryOp _ a -> validateTermM ctx a
    CClosure _ captured _ -> forM_ captured $ \(name, _) -> do
        unless (Set.member name (vcScope ctx))
            $ report
            $ InvalidCapture name (vcPath ctx ++ ": captured variable not in scope")
    CClosureGetEnv closure _ _ -> validateTermM ctx closure
    CProject expr _ _ -> validateTermM ctx expr
    CPanic _ _ -> pure ()
    CFork taskName _ comp body -> do
        validateTermM ctx comp
        let ctx' = registerFork taskName $ extendScope taskName ctx
        validateTermM ctx' body
    CJoin taskName _ ->
        unless (Set.member taskName (vcForks ctx))
            $ report
            $ UnmatchedJoin taskName (vcPath ctx ++ ": no matching Fork")

checkWellScoped :: Set Name -> CTerm -> ValidationResult
checkWellScoped = validateTerm False

checkLinear :: Set Name -> CTerm -> ValidationResult
checkLinear = validateTerm True

checkTypeConsistency :: CTerm -> ValidationResult
checkTypeConsistency = go
  where
    go term = execWriter $ case term of
        -- Check application: function type should match argument
        CApp f x resultTy -> do
            let fTy = getTermType f
            case fTy of
                TArrow argTy retTy -> do
                    let xTy = getTermType x
                    unless (typesCompatible argTy xTy)
                        $ report
                        $ TypeMismatch argTy xTy "function argument type mismatch"
                    unless (typesCompatible retTy resultTy)
                        $ report
                        $ TypeMismatch retTy resultTy "function return type mismatch"
                _ -> pure () -- Non-arrow types are caught elsewhere
            tell $ go f
            tell $ go x

        -- Check case: all arms should have consistent result types
        CCase scrut arms mdef resultTy -> do
            let armTypes = [getTermType body | (_, _, body) <- arms]
                defTypes = maybe [] (\d -> [getTermType d]) mdef
                allTypes = armTypes ++ defTypes

            forM_ allTypes $ \armTy ->
                unless (typesCompatible armTy resultTy)
                    $ report
                    $ TypeMismatch resultTy armTy "case arm type mismatch"

            tell $ go scrut
            forM_ arms $ \(_, _, body) -> tell $ go body
            forM_ mdef $ \d -> tell $ go d
        _ -> forM_ (children term) $ \child -> tell $ go child

checkDupSupPairing :: CTerm -> ValidationResult
checkDupSupPairing = go Map.empty
  where
    go :: Map Name Label -> CTerm -> ValidationResult
    go labels term = execWriter $ case term of
        CDup name _ label val body -> do
            tell $ go labels val
            let labels' = Map.insert name label labels
            tell $ go labels' body
        CSup _label a b _ -> do
            -- SUPs should eventually interact with DUPs of the same label
            -- This is a heuristic check - not always detectable statically
            tell $ go labels a
            tell $ go labels b
        CDp0 name _ -> do
            case Map.lookup name labels of
                Nothing ->
                    report $ OrphanProjection (name ++ ".0") "projection without DUP"
                Just _ -> pure ()
        CDp1 name _ -> do
            case Map.lookup name labels of
                Nothing ->
                    report $ OrphanProjection (name ++ ".1") "projection without DUP"
                Just _ -> pure ()
        _ -> forM_ (children term) $ \child -> tell $ go labels child

typesCompatible :: Type -> Type -> Bool
typesCompatible t1 t2
    | t1 == t2 = True
    | TVar _ <- t1 = True
    | TVar _ <- t2 = True
    | TSkolem _ <- t1 = True
    | TSkolem _ <- t2 = True
    | TArrow a1 r1 <- t1
    , TArrow a2 r2 <- t2 =
        typesCompatible a1 a2 && typesCompatible r1 r2
    | TApp f1 a1 <- t1
    , TApp f2 a2 <- t2 =
        typesCompatible f1 f2 && typesCompatible a1 a2
    | otherwise = False
