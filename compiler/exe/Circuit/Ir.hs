{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

{- | Circuit IR: An Interaction Net-based intermediate representation.

This IR represents programs as interaction nets, enabling optimal
reduction through local graph rewriting. The key concepts are:

* Variables can be used multiple times (non-affine) before linearization
* After linearization, each variable is used exactly once (affine)
* Duplications (DUP) and erasures (ERA) make sharing/discarding explicit
* Superpositions (SUP) represent "cloned" values with labels

The compilation pipeline is:
  Metal -> Circuit (non-affine) -> Linearize -> Circuit (affine) -> Alloy/Eval
-}
module Circuit.Ir (
    Name,
    Label,
    CTerm (..),
    BinOp (..),
    CmpOp (..),
    UnaryOp (..),
    CFunction (..),
    CFunctionMeta (..),
    CTypeDef (..),
    CConstructor (..),
    CModule (..),
    defaultFunctionMeta,
    mkFunction,
    emptyModule,
    children,
    mapChildren,
    foldChildren,
    mapChildrenM,
    transformBottomUp,
    transformTopDown,
    universe,
    getTermType,
    countVarUses,
    freeVars,
    freeVarsWithTypes,
    isLinear,
    AllocKind (..),
    classifyType,
    classifyTypeWithEnv,
    classifyTerm,
    mergeAllocKind,
) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Monoid (Sum (..))
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Project.Name (Name (..))
import Typing.Types (TyConstructor (..), TyPrimitive (..), TyUnique (..), Type (..), boolType, intType, strType, unitType)

{- | A label distinguishes different superposition/duplication pairs.
When a DUP with label L meets a SUP with label L, they annihilate.
Different labels cause commutation (nested duplication).
-}
type Label = Int

{- | Circuit terms - the core expression language.

Before linearization, variables (CVar) may appear multiple times.
After linearization, each CVar appears exactly once, and CDup nodes
are inserted to make sharing explicit.
-}
data CTerm
    = -- | Variable reference with type. After linearization, used exactly once.
      CVar !Name !Type
    | {- | Lambda abstraction: λ(x : T). body
      The bound variable may be used zero, one, or multiple times
      in body (before linearization). Includes parameter type.
      -}
      CLam !Name !Type !CTerm
    | {- | Application: (f x) with result type
      Call-by-value: x is evaluated before substitution.
      -}
      CApp !CTerm !CTerm !Type
    | {- | Let binding: let (x : T) = val in body
      Strict: val is evaluated before binding. Includes binding type.
      -}
      CLet !Name !Type !CTerm !CTerm
    | {- | Superposition: &L{a, b} with element type
      Represents a value that has been "split" into two copies
      with label L. Used by duplication.
      -}
      CSup !Label !CTerm !CTerm !Type
    | {- | Duplication: !(x : T) &L = val; body
      Splits val into two parts accessible as x₀ and x₁.
      x₀ = CDp0 x, x₁ = CDp1 x. Includes the type of the duplicated value.
      -}
      CDup !Name !Type !Label !CTerm !CTerm
    | -- | First projection of a duplicated value (x₀) with type
      CDp0 !Name !Type
    | -- | Second projection of a duplicated value (x₁) with type
      CDp1 !Name !Type
    | {- | Erasure: represents a discarded value
      When something is duplicated but one copy isn't used.
      -}
      CEra
    | {- | Erase/consume a value and continue with body.
      CErase valueToDiscard body
      Used to linearly consume unused variables (e.g., unused function parameters).
      The value is evaluated/consumed, then the body is evaluated.
      -}
      CErase !CTerm !CTerm
    | {- | Function reference: @name with type
      References a top-level definition.
      -}
      CRef !Name !Type
    | -- | Integer literal
      CInt !Int
    | -- | Boolean literal (encoded as 0/1 or λλ encoding)
      CBool !Bool
    | -- | String literal
      CStr !String
    | {- | Tagged value for ADT constructors: <tag, field0, field1, ...> with result type
      tag is an integer, fields are the constructor's data.
      For nullary constructors, fields is empty [].
      -}
      CTag !Int ![CTerm] !Type
    | {- | Case/switch on a tagged value with result type
      CCase scrutinee [(tag, [(fieldName, fieldType)], body)] default resultType
      Each body receives the fields of the matched tag bound to fieldNames.
      -}
      CCase !CTerm ![(Int, [(Name, Type)], CTerm)] !(Maybe CTerm) !Type
    | -- | Binary primitive operation (result is always Int)
      CBinOp !BinOp !CTerm !CTerm
    | -- | Comparison operation (result is always Bool)
      CCmpOp !CmpOp !CTerm !CTerm
    | -- | Unary primitive operation
      CUnaryOp !UnaryOp !CTerm
    | {- | Closure: a lifted function with captured environment
      CClosure liftedFuncName capturedVars closureType
      where capturedVars is [(name, type)] of variables to capture
      -}
      CClosure !Name ![(Name, Type)] !Type
    | {- | Extract a captured variable from a closure's environment
      CClosureGetEnv closure index resultType
      Used to extract captured variables in lambda function bodies.
      -}
      CClosureGetEnv !CTerm !Int !Type
    | {- | Project a field from a tagged value (record/tuple/constructor)
      CProject expr fieldIndex resultType
      -}
      CProject !CTerm !Int !Type
    | {- | Panic: abort execution with an error message
      CPanic message resultType
      The result type is needed for type consistency in expressions.
      -}
      CPanic !String !Type
    | {- | Fork: spawn a computation as a parallel task
        CFork taskName resultType computation continuation
        - taskName: name for the task handle
        - resultType: type of the computation's result
        - computation: the expression to evaluate in parallel
        - continuation: what to do after forking (doesn't wait)
      -}
      CFork !Name !Type !CTerm !CTerm
    | {- | Join: wait for a forked task and get its result
        CJoin taskName resultType
        - taskName: the task handle from CFork
        - resultType: type of the result
        Blocks until the task completes, then returns its result.
      -}
      CJoin !Name !Type
    deriving (Show, Eq, Generic)

-- | Binary operations on primitives
data BinOp
    = OpAdd
    | OpSub
    | OpMul
    | OpDiv
    | OpMod
    | OpAnd
    | OpOr
    | OpXor
    | OpShl
    | OpShr
    deriving (Show, Eq, Generic)

-- | Comparison operations
data CmpOp
    = OpEq
    | OpNe
    | OpLt
    | OpLe
    | OpGt
    | OpGe
    deriving (Show, Eq, Generic)

-- | Unary operations
data UnaryOp
    = OpNot
    | OpNeg
    deriving (Show, Eq, Generic)

-- | A top-level function definition
data CFunction = CFunction
    { cfName :: !Name
    , cfParams :: ![(Name, Type)]
    -- ^ Parameter names with their types
    , cfReturnType :: !Type
    -- ^ Return type of the function
    , cfBody :: !CTerm
    , cfMetadata :: !CFunctionMeta
    }
    deriving (Show, Eq, Generic)

-- | Metadata about a function
data CFunctionMeta = CFunctionMeta
    { cfmArity :: !Int
    -- ^ Number of parameters
    , cfmIsLinear :: !Bool
    -- ^ Whether the function has been linearized
    }
    deriving (Show, Eq, Generic)

-- | A type definition (ADT) - for reference during lowering
data CTypeDef = CTypeDef
    { ctName :: !Name
    , ctConstructors :: ![CConstructor]
    }
    deriving (Show, Eq, Generic)

-- | A constructor in an ADT
data CConstructor = CConstructor
    { ccName :: !Name
    , ccTag :: !Int
    , ccArity :: !Int -- Number of fields
    }
    deriving (Show, Eq, Generic)

-- | A complete Circuit module
data CModule = CModule
    { cmName :: !String
    , cmFunctions :: ![CFunction]
    , cmTypes :: ![CTypeDef]
    , cmIsLinearized :: !Bool
    -- ^ Whether the module has gone through linearization
    , cmExternalRefs :: ![Name]
    -- ^ External function references that are valid but not defined in this module
    }
    deriving (Show, Eq, Generic)

-- | Default function metadata
defaultFunctionMeta :: Int -> CFunctionMeta
defaultFunctionMeta arity =
    CFunctionMeta
        { cfmArity = arity
        , cfmIsLinear = False
        }

-- | Create a simple function with typed parameters
mkFunction :: Name -> [(Name, Type)] -> Type -> CTerm -> CFunction
mkFunction name params retTy body =
    CFunction
        { cfName = name
        , cfParams = params
        , cfReturnType = retTy
        , cfBody = body
        , cfMetadata = defaultFunctionMeta (length params)
        }

-- | Create an empty module
emptyModule :: String -> CModule
emptyModule name =
    CModule
        { cmName = name
        , cmFunctions = []
        , cmTypes = []
        , cmIsLinearized = False
        , cmExternalRefs = []
        }

-- ============================================================================
-- Term Traversal Helpers
-- ============================================================================

{- | Get all immediate child terms of a CTerm.

This is the foundation for generic traversals. Note that this does NOT
recurse into children - it only returns the direct children.

For binding forms (CLam, CLet, CDup, CCase arms), children include
the bodies where variables are bound.
-}
children :: CTerm -> [CTerm]
children = \case
    -- Leaf nodes (no children)
    CVar{} -> []
    CDp0{} -> []
    CDp1{} -> []
    CEra -> []
    CRef{} -> []
    CInt{} -> []
    CBool{} -> []
    CStr{} -> []
    CPanic{} -> []
    CJoin{} -> []
    -- Single child
    CLam _ _ body -> [body]
    CUnaryOp _ a -> [a]
    CClosureGetEnv e _ _ -> [e]
    CProject e _ _ -> [e]
    -- Two children
    CApp f x _ -> [f, x]
    CLet _ _ val body -> [val, body]
    CSup _ a b _ -> [a, b]
    CDup _ _ _ val body -> [val, body]
    CErase val body -> [val, body]
    CBinOp _ a b -> [a, b]
    CCmpOp _ a b -> [a, b]
    CFork _ _ comp cont -> [comp, cont]
    -- Multiple children
    CTag _ fields _ -> fields
    CCase scrut arms mdef _ ->
        scrut : [body | (_, _, body) <- arms] ++ maybe [] pure mdef
    -- CClosure has no CTerm children (captured vars are names, not terms)
    CClosure{} -> []

{- | Map a function over all immediate child terms.

This reconstructs the term with transformed children. Use this for
transformations that don't need binding context.

For binding-aware transformations, you'll still need custom recursion
to track which variables are in scope.
-}
mapChildren :: (CTerm -> CTerm) -> CTerm -> CTerm
mapChildren f = \case
    -- Leaf nodes (unchanged)
    t@CVar{} -> t
    t@CDp0{} -> t
    t@CDp1{} -> t
    t@CEra -> t
    t@CRef{} -> t
    t@CInt{} -> t
    t@CBool{} -> t
    t@CStr{} -> t
    t@CPanic{} -> t
    t@CJoin{} -> t
    t@CClosure{} -> t
    -- Single child
    CLam n ty body -> CLam n ty (f body)
    CUnaryOp op a -> CUnaryOp op (f a)
    CClosureGetEnv e idx ty -> CClosureGetEnv (f e) idx ty
    CProject e idx ty -> CProject (f e) idx ty
    -- Two children
    CApp fun arg ty -> CApp (f fun) (f arg) ty
    CLet n ty val body -> CLet n ty (f val) (f body)
    CSup l a b ty -> CSup l (f a) (f b) ty
    CDup n ty l val body -> CDup n ty l (f val) (f body)
    CErase val body -> CErase (f val) (f body)
    CBinOp op a b -> CBinOp op (f a) (f b)
    CCmpOp op a b -> CCmpOp op (f a) (f b)
    CFork n ty comp cont -> CFork n ty (f comp) (f cont)
    -- Multiple children
    CTag tag fields ty -> CTag tag (map f fields) ty
    CCase scrut arms mdef ty ->
        CCase (f scrut) [(t, ns, f body) | (t, ns, body) <- arms] (f <$> mdef) ty

{- | Fold over all immediate child terms with a monoidal result.

This is useful for collecting information from all children.
For binding-aware collection, you'll still need custom recursion.
-}
foldChildren :: (Monoid m) => (CTerm -> m) -> CTerm -> m
foldChildren f term = mconcat (map f (children term))

{- | Monadic version of mapChildren for effectful traversals.

Useful for transformations that need state (like fresh name generation)
or other effects. Traverses children left-to-right.
-}
mapChildrenM :: (Monad m) => (CTerm -> m CTerm) -> CTerm -> m CTerm
mapChildrenM f = \case
    -- Leaf nodes (unchanged)
    t@CVar{} -> pure t
    t@CDp0{} -> pure t
    t@CDp1{} -> pure t
    t@CEra -> pure t
    t@CRef{} -> pure t
    t@CInt{} -> pure t
    t@CBool{} -> pure t
    t@CStr{} -> pure t
    t@CPanic{} -> pure t
    t@CJoin{} -> pure t
    t@CClosure{} -> pure t
    -- Single child
    CLam n ty body -> CLam n ty <$> f body
    CUnaryOp op a -> CUnaryOp op <$> f a
    CClosureGetEnv e idx ty -> (\e' -> CClosureGetEnv e' idx ty) <$> f e
    CProject e idx ty -> (\e' -> CProject e' idx ty) <$> f e
    -- Two children
    CApp fun arg ty -> CApp <$> f fun <*> f arg <*> pure ty
    CLet n ty val body -> CLet n ty <$> f val <*> f body
    CSup l a b ty -> CSup l <$> f a <*> f b <*> pure ty
    CDup n ty l val body -> CDup n ty l <$> f val <*> f body
    CErase val body -> CErase <$> f val <*> f body
    CBinOp op a b -> CBinOp op <$> f a <*> f b
    CCmpOp op a b -> CCmpOp op <$> f a <*> f b
    CFork n ty comp cont -> CFork n ty <$> f comp <*> f cont
    -- Multiple children
    CTag tag fields ty -> CTag tag <$> traverse f fields <*> pure ty
    CCase scrut arms mdef ty -> do
        scrut' <- f scrut
        arms' <- traverse (\(t, ns, body) -> (t,ns,) <$> f body) arms
        mdef' <- traverse f mdef
        pure $ CCase scrut' arms' mdef' ty

{- | Transform a term bottom-up (children first, then the term itself).

Applies the function to all subterms, starting from the leaves.
Useful for simplification passes that don't need binding context.
-}
transformBottomUp :: (CTerm -> CTerm) -> CTerm -> CTerm
transformBottomUp f = go
  where
    go term = f (mapChildren go term)

{- | Transform a term top-down (term first, then children).

Applies the function to the term, then recursively to children.
Useful when the transformation of children depends on the parent.
-}
transformTopDown :: (CTerm -> CTerm) -> CTerm -> CTerm
transformTopDown f = go
  where
    go term = mapChildren go (f term)

{- | Recursively collect all subterms (including the term itself).

Returns a list of all terms in the tree, in pre-order traversal.
-}
universe :: CTerm -> [CTerm]
universe term = term : concatMap universe (children term)

-- ============================================================================
-- Type Extraction
-- ============================================================================

-- | Get the type of a Circuit term
getTermType :: CTerm -> Type
getTermType = \case
    CVar _ ty -> ty
    CLam _ paramTy body -> TArrow paramTy (getTermType body)
    CApp _ _ ty -> ty
    CLet _ _ _ body -> getTermType body
    CSup _ _ _ ty -> ty
    CDup _ _ _ _ body -> getTermType body
    CErase _ body -> getTermType body
    CDp0 _ ty -> ty
    CDp1 _ ty -> ty
    CEra -> unitType
    CRef _ ty -> ty
    CInt _ -> intType
    CBool _ -> boolType
    CStr _ -> strType
    CTag _ _ ty -> ty
    CCase _ _ _ ty -> ty
    CBinOp{} -> intType
    CCmpOp{} -> boolType
    CUnaryOp op _ -> case op of
        OpNot -> boolType
        OpNeg -> intType
    CClosure _ _ ty -> ty
    CClosureGetEnv _ _ ty -> ty
    CProject _ _ ty -> ty
    CPanic _ ty -> ty
    CFork _ ty _ _ -> ty
    CJoin _ ty -> ty

-- ============================================================================
-- Variable Analysis
-- ============================================================================

{- | Count variable occurrences in a term.

This is binding-aware: occurrences under a binder that shadows
the target variable are not counted.
-}
countVarUses :: Name -> CTerm -> Int
countVarUses target = go
  where
    go term = case term of
        -- Variable references
        CVar n _ -> if n == target then 1 else 0
        CDp0 n _ -> if n == target then 1 else 0
        CDp1 n _ -> if n == target then 1 else 0
        -- Binding forms: check for shadowing
        CLam n _ body -> if n == target then 0 else go body
        CLet n _ val body -> go val + if n == target then 0 else go body
        CDup n _ _ val body -> go val + if n == target then 0 else go body
        CCase scrut arms mdef _ ->
            go scrut
                + sum [if target `elem` map fst ns then 0 else go body | (_, ns, body) <- arms]
                + maybe 0 go mdef
        -- CClosure captures variables by name
        CClosure _ captured _ -> sum [if n == target then 1 else 0 | (n, _) <- captured]
        -- All other nodes: sum over children
        _ -> getSum $ foldChildren (Sum . go) term

{- | Get all free variables in a term.

This is binding-aware: variables bound by CLam, CLet, CDup, or CCase
pattern bindings are not considered free in their scope.
-}
freeVars :: CTerm -> Set Name
freeVars = go Set.empty
  where
    go bound term = case term of
        -- Variable references
        CVar n _ -> if Set.member n bound then Set.empty else Set.singleton n
        CDp0 n _ -> if Set.member n bound then Set.empty else Set.singleton n
        CDp1 n _ -> if Set.member n bound then Set.empty else Set.singleton n
        -- Binding forms: extend bound set
        CLam n _ body -> go (Set.insert n bound) body
        CLet n _ val body -> go bound val <> go (Set.insert n bound) body
        CDup n _ _ val body -> go bound val <> go (Set.insert n bound) body
        CCase scrut arms mdef _ ->
            go bound scrut
                <> mconcat [go (foldr (Set.insert . fst) bound ns) body | (_, ns, body) <- arms]
                <> maybe Set.empty (go bound) mdef
        -- CClosure captures variables by name
        CClosure _ captured _ ->
            Set.fromList [n | (n, _) <- captured, not (Set.member n bound)]
        -- All other nodes: union over children
        _ -> foldChildren (go bound) term

{- | Get all free variables in a term with their types.

Same as 'freeVars' but also returns the type of each variable.
-}
freeVarsWithTypes :: CTerm -> Map Name Type
freeVarsWithTypes = go Set.empty
  where
    go bound term = case term of
        -- Variable references with types
        CVar n ty -> if Set.member n bound then Map.empty else Map.singleton n ty
        CDp0 n ty -> if Set.member n bound then Map.empty else Map.singleton n ty
        CDp1 n ty -> if Set.member n bound then Map.empty else Map.singleton n ty
        -- Binding forms: extend bound set
        CLam n _ body -> go (Set.insert n bound) body
        CLet n _ val body -> go bound val <> go (Set.insert n bound) body
        CDup n _ _ val body -> go bound val <> go (Set.insert n bound) body
        CCase scrut arms mdef _ ->
            go bound scrut
                <> mconcat [go (foldr (Set.insert . fst) bound ns) body | (_, ns, body) <- arms]
                <> maybe Map.empty (go bound) mdef
        -- CClosure captures variables by name with types
        CClosure _ captured _ ->
            Map.fromList [(n, ty) | (n, ty) <- captured, not (Set.member n bound)]
        -- All other nodes: union over children
        _ -> foldChildren (go bound) term

-- | Check if a term is linear (all variables used exactly once)
isLinear :: CTerm -> Bool
isLinear term = all (\v -> countVarUses v term == 1) (Set.toList $ freeVars term)

-- ============================================================================
-- Allocation Classification
-- ============================================================================

{- | Allocation kind for memory management.

This determines whether a value lives on the stack (immediate, freed automatically)
or the heap (needs explicit deallocation via ERA nodes).

The key insight: After linearization, every value is used exactly once.
This means we don't need GC - we know exactly when to free each value.

- StackOnly: Primitives, ADTs with only stack fields. Freed when scope exits.
- MaybeHeap: Closures, SUPs, ADTs with heap fields. Freed by ERA nodes.
-}
data AllocKind
    = {- | Immediate value, no heap allocation needed.
      Includes: Int, Bool, Char, and ADTs where all fields are StackOnly.
      -}
      StackOnly
    | {- | May require heap allocation.
      Includes: Functions/closures, SUPs, ADTs with MaybeHeap fields,
      polymorphic types, or unknown types.
      -}
      MaybeHeap
    deriving (Show, Eq, Generic)

-- | Classify a Metal type into an allocation kind
classifyType :: Type -> AllocKind
classifyType = classifyTypeWithEnv Map.empty

-- | Classify a type with an environment of known type allocation kinds
classifyTypeWithEnv :: Map Name AllocKind -> Type -> AllocKind
classifyTypeWithEnv env ty = case ty of
    -- Primitive types are always stack-allocated
    TConstructor tc -> case tcId tc of
        TyPrim prim | prim `elem` [TPInt, TPBool, TPByte, TPUnit] -> StackOnly
        _ -> MaybeHeap -- User-defined types may be heap-allocated
        -- Function types are heap-allocated (closures)
    TArrow _ _ -> MaybeHeap
    -- Type variables are conservatively MaybeHeap (polymorphic)
    TVar _ -> MaybeHeap
    -- Skolem variables are MaybeHeap (unknown concrete type)
    TSkolem _ -> MaybeHeap
    -- Type application: check the result
    -- e.g., Maybe Int -> depends on Maybe's definition
    TApp f _ -> classifyTypeWithEnv env f
    -- Unresolved types are conservatively MaybeHeap
    TUnresolved _ -> MaybeHeap

{- | Classify a Circuit term based on its structure
Returns StackOnly if the term produces a stack value, MaybeHeap otherwise
-}
classifyTerm :: CTerm -> AllocKind
classifyTerm = \case
    -- Primitives are stack-allocated
    CInt _ -> StackOnly
    CBool _ -> StackOnly
    CStr _ -> StackOnly -- Note: strings might need heap in practice

    -- Variables: use the type annotation to determine allocation
    CVar _ ty -> classifyType ty
    -- Lambdas are closures -> heap
    CLam{} -> MaybeHeap
    -- Applications: use the result type annotation
    CApp _ _ ty -> classifyType ty
    -- Let: the body determines the allocation
    CLet _ _ _ body -> classifyTerm body
    -- Superpositions are always heap-allocated
    CSup{} -> MaybeHeap
    -- Duplications: body determines the allocation
    CDup _ _ _ _ body -> classifyTerm body
    -- Erasure: body determines the allocation
    CErase _ body -> classifyTerm body
    -- Projections: use the type annotation
    CDp0 _ ty -> classifyType ty
    CDp1 _ ty -> classifyType ty
    -- Erasure produces nothing (stack/no value)
    CEra -> StackOnly
    -- Function reference: use the type annotation
    CRef _ ty -> classifyType ty
    -- Tagged values: use the type annotation
    CTag _ _ ty -> classifyType ty
    -- Case: use the result type annotation
    CCase _ _ _ ty -> classifyType ty
    -- Primitive ops produce stack values
    CBinOp{} -> StackOnly
    CCmpOp{} -> StackOnly
    CUnaryOp _ _ -> StackOnly
    -- Closures are heap-allocated (contain environment)
    CClosure{} -> MaybeHeap
    -- Closure env access: use the result type annotation
    CClosureGetEnv _ _ ty -> classifyType ty
    -- Field projection: use the result type annotation
    CProject _ _ ty -> classifyType ty
    -- Panic: never returns, but use the declared type for consistency
    CPanic _ ty -> classifyType ty
    -- Fork: the continuation determines allocation
    -- The forked computation runs in parallel, but the continuation's result type matters
    CFork _ _ _ cont -> classifyTerm cont
    -- Join: use the result type annotation
    -- Blocks until the task completes, result type matters
    CJoin _ ty -> classifyType ty

-- | Merge two allocation kinds (conservative: if either is MaybeHeap, result is MaybeHeap)
mergeAllocKind :: AllocKind -> AllocKind -> AllocKind
mergeAllocKind StackOnly StackOnly = StackOnly
mergeAllocKind _ _ = MaybeHeap
