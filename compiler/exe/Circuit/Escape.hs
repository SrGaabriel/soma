{-# LANGUAGE RecordWildCards #-}

{- | Escape Analysis for Circuit IR.

This pass determines whether closures "escape" their definition scope,
enabling clone elision optimizations. A closure that doesn't escape
can be duplicated without creating SUP nodes - both copies are used
in the same local context and don't need lazy cloning.

Escape Classifications:
  - NoEscape: Closure is created and fully consumed in the same scope.
              Safe to skip SUP wrapping; use direct copy.
  - LocalEscape: Closure escapes to a local let binding but not returned.
                 May benefit from stack allocation.
  - Escapes: Closure is returned, stored in a data structure, or passed
             to an unknown function. Requires full SUP-based lazy cloning.

The analysis is conservative: if we can't prove a closure doesn't escape,
we assume it does (Escapes).

Key Optimization: When a closure is duplicated (CDup) and neither projection
escapes, we can:
  1. Skip OpDupClosure/OpDupClosureProj* entirely
  2. Use direct closure copying (memcpy-style)
  3. Avoid SUP allocation overhead for nested closure slots
-}
module Circuit.Escape (
    -- * Escape Analysis
    EscapeKind (..),
    EscapeEnv,
    analyzeEscapes,
    analyzeFunctionEscapes,

    -- * Environment operations
    lookupEscape,
    doesEscape,
    canElideClone,
) where

import Circuit.Ir
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Typing.Types (Type (..))

-- | Escape classification for a binding
data EscapeKind
    = -- | Value is used only in local scope, never returned or stored
      NoEscape
    | -- | Value escapes to a local binding but not beyond the function
      LocalEscape
    | -- | Value may escape the function (returned, stored in heap structure, etc.)
      Escapes
    deriving (Show, Eq, Ord)

-- | Environment mapping variable names to their escape status
type EscapeEnv = Map Name EscapeKind

-- | Context for escape analysis
data EscapeContext
    = -- | In a local expression context (let body, case body, etc.)
      CtxLocal
    | -- | In return position (function body, let value that's returned)
      CtxReturn
    | -- | Being passed as argument to unknown function
      CtxArg
    | -- | Being stored in a data structure
      CtxStore
    deriving (Show, Eq)

-- | Analysis state tracking what we know about each binding
data AnalysisState = AnalysisState
    { asEscapes :: Map Name EscapeKind
    -- ^ Current escape status for each binding
    , asClosures :: Set Name
    -- ^ Names that are bound to closures
    , asDupProjections :: Map Name Name
    -- ^ Maps projection names (x.0, x.1) to their DUP source
    }

emptyState :: AnalysisState
emptyState = AnalysisState Map.empty Set.empty Map.empty

-- | Merge two escape kinds (conservative: take the "more escaped" one)
mergeEscape :: EscapeKind -> EscapeKind -> EscapeKind
mergeEscape Escapes _ = Escapes
mergeEscape _ Escapes = Escapes
mergeEscape LocalEscape _ = LocalEscape
mergeEscape _ LocalEscape = LocalEscape
mergeEscape NoEscape NoEscape = NoEscape

-- | Update escape status for a name
updateEscape :: Name -> EscapeKind -> AnalysisState -> AnalysisState
updateEscape name kind st =
    let current = Map.findWithDefault NoEscape name (asEscapes st)
        merged = mergeEscape current kind
    in st{asEscapes = Map.insert name merged (asEscapes st)}

-- | Mark a name as a closure
markClosure :: Name -> AnalysisState -> AnalysisState
markClosure name st = st{asClosures = Set.insert name (asClosures st)}

-- | Register a DUP projection
registerProjection :: Name -> Name -> AnalysisState -> AnalysisState
registerProjection projName srcName st =
    st{asDupProjections = Map.insert projName srcName (asDupProjections st)}

-- | Analyze escape status for all bindings in a module
analyzeEscapes :: CModule -> EscapeEnv
analyzeEscapes CModule{..} =
    Map.unions $ map analyzeFunctionEscapes cmFunctions

-- | Analyze escape status for bindings in a function
analyzeFunctionEscapes :: CFunction -> EscapeEnv
analyzeFunctionEscapes CFunction{..} =
    let initState = emptyState
        -- Analyze the body in return context (function result escapes)
        finalState = analyzeTermEscapes CtxReturn cfBody initState
    in asEscapes finalState

-- | Analyze a term and update escape status
analyzeTermEscapes :: EscapeContext -> CTerm -> AnalysisState -> AnalysisState
analyzeTermEscapes ctx term st = case term of
    -- Variables: mark as escaping based on context
    CVar name _ ->
        let kind = contextToEscape ctx
        in updateEscape name kind st
    -- Lambda: the lambda itself may escape, analyze body locally
    CLam _ _ body ->
        let st' = analyzeTermEscapes CtxLocal body st
        in st'
    -- Application: function and arg are used, result depends on context
    -- Key insight: if we're calling a known lifted lambda with a closure as
    -- the first arg (closure_self pattern), that doesn't constitute escape
    -- because the lifted function uses it locally.
    CApp f x _ ->
        let
            -- Check if this is a call to a known function (not indirect)
            isDirectCall = case f of
                CRef _ _ -> True
                CVar _ _ -> True
                CApp{} -> True -- Curried application
                _ -> False
            -- For direct calls, arguments are used locally (don't escape)
            -- For indirect calls, arguments may escape anywhere
            argCtx = if isDirectCall then CtxLocal else CtxArg
            st1 = analyzeTermEscapes CtxLocal f st -- function ref is used locally
            st2 = analyzeTermEscapes argCtx x st1 -- arg context depends on call type
        in
            st2
    -- Let binding: analyze value and body
    CLet name ty val body ->
        let
            -- Check if this binding is a closure
            isClosure = isClosureType ty || isClosureTerm val
            st0 = if isClosure then markClosure name st else st
            -- Value context depends on whether body returns it
            valCtx =
                if nameUsedInReturnPosition name body
                    then CtxReturn
                    else CtxLocal
            st1 = analyzeTermEscapes valCtx val st0
            -- Body is in the same context as the let
            st2 = analyzeTermEscapes ctx body st1
            -- If name isn't used, it doesn't escape
            st3 =
                if countVarUses name body == 0
                    then updateEscape name NoEscape st2
                    else st2
        in
            st3
    -- Superposition: both branches may be used
    CSup _ a b _ ->
        let st1 = analyzeTermEscapes ctx a st
            st2 = analyzeTermEscapes ctx b st1
        in st2
    -- Duplication: the key case for clone elision!
    CDup name ty _ val body ->
        let
            -- Register this as a closure if it has function type
            isClosure = isClosureType ty
            st0 = if isClosure then markClosure name st else st
            -- Register the projections
            st1 =
                registerProjection (name ++ ".0") name
                    $ registerProjection (name ++ ".1") name st0
            -- Analyze the value being duplicated
            st2 = analyzeTermEscapes CtxLocal val st1
            -- Analyze body to see how projections are used
            st3 = analyzeTermEscapes ctx body st2
            -- Determine escape status for the DUP based on projection usage
            proj0Escape = Map.findWithDefault NoEscape (name ++ ".0") (asEscapes st3)
            proj1Escape = Map.findWithDefault NoEscape (name ++ ".1") (asEscapes st3)
            dupEscape = mergeEscape proj0Escape proj1Escape
            st4 = updateEscape name dupEscape st3
        in
            st4
    -- Projections: mark usage based on context
    CDp0 name _ ->
        let projName = name ++ ".0"
            kind = contextToEscape ctx
        in updateEscape projName kind st
    CDp1 name _ ->
        let projName = name ++ ".1"
            kind = contextToEscape ctx
        in updateEscape projName kind st
    -- Erasure: nothing escapes
    CEra -> st
    -- Function reference: escapes based on context
    CRef name _ ->
        updateEscape name (contextToEscape ctx) st
    -- Literals: no escape tracking needed
    CInt _ -> st
    CBool _ -> st
    CStr _ -> st
    -- Tagged value: fields may escape if the tag escapes
    CTag _ fields _ ->
        let fieldCtx = CtxStore
        in foldr (analyzeTermEscapes fieldCtx) st fields
    -- Case: scrutinee is used, branches depend on context
    CCase scrut arms mdef _ ->
        let st1 = analyzeTermEscapes CtxLocal scrut st
            st2 = foldr (\(_, _, body) s -> analyzeTermEscapes ctx body s) st1 arms
            st3 = maybe st2 (\d -> analyzeTermEscapes ctx d st2) mdef
        in st3
    -- Binary/comparison/unary ops: operands don't escape
    CBinOp _ a b ->
        let st1 = analyzeTermEscapes CtxLocal a st
            st2 = analyzeTermEscapes CtxLocal b st1
        in st2
    CCmpOp _ a b ->
        let st1 = analyzeTermEscapes CtxLocal a st
            st2 = analyzeTermEscapes CtxLocal b st1
        in st2
    CUnaryOp _ a ->
        analyzeTermEscapes CtxLocal a st
    -- Closure: mark captured variables as potentially escaping
    CClosure _ captured _ ->
        let capturedCtx = if ctx == CtxReturn then Escapes else LocalEscape
        in foldr (\(n, _) s -> updateEscape n capturedCtx s) st captured
    -- Closure env access: analyze the closure term
    CClosureGetEnv closure _ _ ->
        analyzeTermEscapes CtxLocal closure st

-- | Convert context to escape kind
contextToEscape :: EscapeContext -> EscapeKind
contextToEscape CtxLocal = NoEscape
contextToEscape CtxReturn = Escapes
contextToEscape CtxArg = Escapes -- Conservative: args may escape
contextToEscape CtxStore = Escapes

-- | Check if a type is a closure/function type
isClosureType :: Type -> Bool
isClosureType (TArrow _ _) = True
isClosureType _ = False

-- | Check if a term creates a closure
isClosureTerm :: CTerm -> Bool
isClosureTerm (CClosure{}) = True
isClosureTerm (CLam{}) = True
isClosureTerm (CClosureGetEnv{}) = False
isClosureTerm _ = False

-- | Check if a name is used in return position within a term
nameUsedInReturnPosition :: Name -> CTerm -> Bool
nameUsedInReturnPosition target = go
  where
    go (CVar n _) = n == target
    go (CLam{}) = False -- Body of lambda is not our return
    go (CApp f _ _) = go f -- Function position matters for partial app
    go (CLet _ _ _ body) = go body
    go (CSup{}) = False
    go (CDup _ _ _ _ body) = go body
    go (CDp0 n _) = n ++ ".0" == target
    go (CDp1 n _) = n ++ ".1" == target
    go CEra = False
    go (CRef n _) = n == target
    go (CInt _) = False
    go (CBool _) = False
    go (CStr _) = False
    go (CTag{}) = False
    go (CCase _ arms mdef _) =
        any (\(_, _, body) -> go body) arms || maybe False go mdef
    go (CBinOp{}) = False
    go (CCmpOp{}) = False
    go (CUnaryOp _ _) = False
    go (CClosure{}) = False
    go (CClosureGetEnv{}) = False

-- ============================================================================
-- Query Functions
-- ============================================================================

-- | Look up escape status for a name
lookupEscape :: Name -> EscapeEnv -> EscapeKind
lookupEscape = Map.findWithDefault Escapes

-- | Check if a name escapes (conservative: unknown = escapes)
doesEscape :: Name -> EscapeEnv -> Bool
doesEscape name env = lookupEscape name env == Escapes

{- | Check if we can elide cloning for a duplicated closure
Returns True if both projections don't escape, meaning we can
use direct copying instead of SUP-based lazy cloning
-}
canElideClone :: Name -> EscapeEnv -> Bool
canElideClone dupName env =
    let proj0 = lookupEscape (dupName ++ ".0") env
        proj1 = lookupEscape (dupName ++ ".1") env
    in proj0 /= Escapes && proj1 /= Escapes
