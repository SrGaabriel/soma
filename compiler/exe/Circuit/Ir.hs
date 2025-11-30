{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}

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
module Circuit.Ir where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Typing.Types (Kind (..), TyConstructor (..), Type (..))

{- | A label distinguishes different superposition/duplication pairs.
When a DUP with label L meets a SUP with label L, they annihilate.
Different labels cause commutation (nested duplication).
-}
type Label = Int

-- | Variable names in the Circuit IR
type Name = String

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
    { cmName :: !Name
    , cmFunctions :: ![CFunction]
    , cmTypes :: ![CTypeDef]
    , cmIsLinearized :: !Bool
    -- ^ Whether the module has gone through linearization
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
emptyModule :: Name -> CModule
emptyModule name =
    CModule
        { cmName = name
        , cmFunctions = []
        , cmTypes = []
        , cmIsLinearized = False
        }

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
    CDp0 _ ty -> ty
    CDp1 _ ty -> ty
    CEra -> TConstructor (TypeConstructor "Unit" KindStar)
    CRef _ ty -> ty
    CInt _ -> TConstructor (TypeConstructor "Int" KindStar)
    CBool _ -> TConstructor (TypeConstructor "Bool" KindStar)
    CStr _ -> TConstructor (TypeConstructor "Str" KindStar)
    CTag _ _ ty -> ty
    CCase _ _ _ ty -> ty
    CBinOp{} -> TConstructor (TypeConstructor "Int" KindStar)
    CCmpOp{} -> TConstructor (TypeConstructor "Bool" KindStar)
    CUnaryOp op _ -> case op of
        OpNot -> TConstructor (TypeConstructor "Bool" KindStar)
        OpNeg -> TConstructor (TypeConstructor "Int" KindStar)
    CClosure _ _ ty -> ty
    CClosureGetEnv _ _ ty -> ty
    CProject _ _ ty -> ty
    CPanic _ ty -> ty
    CFork _ _ _ body -> getTermType body -- CFork continues with body
    CJoin _ ty -> ty -- CJoin returns the result type

-- ============================================================================
-- Variable Analysis
-- ============================================================================

-- | Count variable occurrences in a term
countVarUses :: Name -> CTerm -> Int
countVarUses target = go
  where
    go (CVar n _) = if n == target then 1 else 0
    go (CLam n _ body) = if n == target then 0 else go body
    go (CApp f x _) = go f + go x
    go (CLet n _ val body) = go val + if n == target then 0 else go body
    go (CSup _ a b _) = go a + go b
    go (CDup n _ _ val body) = go val + if n == target then 0 else go body
    go (CDp0 n _) = if n == target then 1 else 0
    go (CDp1 n _) = if n == target then 1 else 0
    go CEra = 0
    go (CRef _ _) = 0
    go (CInt _) = 0
    go (CBool _) = 0
    go (CStr _) = 0
    go (CTag _ fields _) = sum (map go fields)
    go (CCase scrut arms def _) =
        go scrut + sum [go body | (_, _, body) <- arms] + maybe 0 go def
    go (CBinOp _ a b) = go a + go b
    go (CCmpOp _ a b) = go a + go b
    go (CUnaryOp _ a) = go a
    go (CClosure _ captured _) = sum [if n == target then 1 else 0 | (n, _) <- captured]
    go (CClosureGetEnv closure _ _) = go closure
    go (CProject expr _ _) = go expr
    go (CPanic _ _) = 0
    go (CFork n _ comp body) = go comp + if n == target then 0 else go body
    go (CJoin n _) = if n == target then 1 else 0

-- | Get all free variables in a term
freeVars :: CTerm -> Set Name
freeVars = go Set.empty
  where
    go bound (CVar n _) = if Set.member n bound then Set.empty else Set.singleton n
    go bound (CLam n _ body) = go (Set.insert n bound) body
    go bound (CApp f x _) = go bound f <> go bound x
    go bound (CLet n _ val body) = go bound val <> go (Set.insert n bound) body
    go bound (CSup _ a b _) = go bound a <> go bound b
    go bound (CDup n _ _ val body) = go bound val <> go (Set.insert n bound) body
    go bound (CDp0 n _) = if Set.member n bound then Set.empty else Set.singleton n
    go bound (CDp1 n _) = if Set.member n bound then Set.empty else Set.singleton n
    go _ CEra = Set.empty
    go _ (CRef _ _) = Set.empty
    go _ (CInt _) = Set.empty
    go _ (CBool _) = Set.empty
    go _ (CStr _) = Set.empty
    go bound (CTag _ fields _) = mconcat (map (go bound) fields)
    go bound (CCase scrut arms def _) =
        go bound scrut
            <> mconcat [go (foldr (Set.insert . fst) bound ns) body | (_, ns, body) <- arms]
            <> maybe Set.empty (go bound) def
    go bound (CBinOp _ a b) = go bound a <> go bound b
    go bound (CCmpOp _ a b) = go bound a <> go bound b
    go bound (CUnaryOp _ a) = go bound a
    go bound (CClosure _ captured _) =
        Set.fromList [n | (n, _) <- captured, not (Set.member n bound)]
    go bound (CClosureGetEnv closure _ _) = go bound closure
    go bound (CProject expr _ _) = go bound expr
    go _ (CPanic _ _) = Set.empty
    go bound (CFork n _ comp body) = go bound comp <> go (Set.insert n bound) body
    go bound (CJoin n _) = if Set.member n bound then Set.empty else Set.singleton n

-- | Get all free variables in a term with their types
freeVarsWithTypes :: CTerm -> Map Name Type
freeVarsWithTypes = go Set.empty
  where
    go bound (CVar n ty) = if Set.member n bound then Map.empty else Map.singleton n ty
    go bound (CLam n _ body) = go (Set.insert n bound) body
    go bound (CApp f x _) = go bound f <> go bound x
    go bound (CLet n _ val body) = go bound val <> go (Set.insert n bound) body
    go bound (CSup _ a b _) = go bound a <> go bound b
    go bound (CDup n _ _ val body) = go bound val <> go (Set.insert n bound) body
    go bound (CDp0 n ty) = if Set.member n bound then Map.empty else Map.singleton n ty
    go bound (CDp1 n ty) = if Set.member n bound then Map.empty else Map.singleton n ty
    go _ CEra = Map.empty
    go _ (CRef _ _) = Map.empty
    go _ (CInt _) = Map.empty
    go _ (CBool _) = Map.empty
    go _ (CStr _) = Map.empty
    go bound (CTag _ fields _) = mconcat (map (go bound) fields)
    go bound (CCase scrut arms def _) =
        go bound scrut
            <> mconcat [go (foldr (Set.insert . fst) bound ns) body | (_, ns, body) <- arms]
            <> maybe Map.empty (go bound) def
    go bound (CBinOp _ a b) = go bound a <> go bound b
    go bound (CCmpOp _ a b) = go bound a <> go bound b
    go bound (CUnaryOp _ a) = go bound a
    go bound (CClosure _ captured _) =
        Map.fromList [(n, ty) | (n, ty) <- captured, not (Set.member n bound)]
    go bound (CClosureGetEnv closure _ _) = go bound closure
    go bound (CProject expr _ _) = go bound expr
    go _ (CPanic _ _) = Map.empty
    go bound (CFork n _ comp body) = go bound comp <> go (Set.insert n bound) body
    go bound (CJoin n ty) = if Set.member n bound then Map.empty else Map.singleton n ty

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
    TConstructor tc
        | tcName tc `elem` ["Int", "Bool", "Byte", "Char", "Unit"] -> StackOnly
        | otherwise ->
            -- Check if we know about this type from the environment
            Map.findWithDefault MaybeHeap (tcName tc) env
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
    CFork _ _ _ body -> classifyTerm body
    -- Join: use the result type annotation
    CJoin _ ty -> classifyType ty

-- | Merge two allocation kinds (conservative: if either is MaybeHeap, result is MaybeHeap)
mergeAllocKind :: AllocKind -> AllocKind -> AllocKind
mergeAllocKind StackOnly StackOnly = StackOnly
mergeAllocKind _ _ = MaybeHeap
