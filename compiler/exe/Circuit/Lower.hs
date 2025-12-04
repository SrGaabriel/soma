{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

{- HLINT ignore "Use newtype instead of data" -}

{- | Lowering from Metal HIR to Circuit IR.

This pass converts Metal's high-level functional representation
into the Interaction Net-based Circuit IR. Key transformations:

* Lambdas and applications map directly
* Let bindings map directly
* ADT constructors become tagged values (CTag)
* Pattern matching becomes CCase with tag dispatch
* Primitives map to Circuit's primitive operations

After lowering, the Circuit IR still has non-affine variables.
A separate linearization pass inserts DUP/ERA nodes.

Note: For lambda functions with captured variables, this pass extracts
the captured variables from the closure_self parameter using CClosureGetEnv.
-}
module Circuit.Lower where

import Circuit.Ir
import Control.Monad (forM)
import Control.Monad.Reader
import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Metal.Expr
import Metal.Function
import Metal.Metadata (ClosureFunctionInfo (..), MetallicFunctionMetadata (..), MetallicTypeClassMetadata (..))
import Metal.Module
import Syntax.Patterns (Literal (..), Pattern (..))
import Typing.Types (Kind (..), QualifiedType (..), TyConstructor (..), Type (..), boolType, closurePtrType, intType)

-- | Environment for lowering
data LowerEnv = LowerEnv
    { leConstructors :: Map String (Int, Int, [Type])
    -- ^ Constructor name -> (tag, arity, field types)
    , leTypeMap :: Map String CTypeDef
    -- ^ Type name -> type definition
    , leFunctions :: Map String Type
    -- ^ Top-level function name -> type (for distinguishing refs from local vars)
    }
    deriving (Show)

-- | State for lowering
data LowerState = LowerState
    { lsNextTmp :: !Int
    -- ^ Counter for temporary variables
    }
    deriving (Show)

type LowerM = ReaderT LowerEnv (State LowerState)

-- | Generate a fresh temporary name
freshTmp :: String -> LowerM Name
freshTmp prefix = do
    s <- get
    put s{lsNextTmp = lsNextTmp s + 1}
    pure (prefix ++ "$" ++ show (lsNextTmp s))

-- | Initial lowering state
initLowerState :: LowerState
initLowerState = LowerState{lsNextTmp = 0}

-- | Build environment from module
buildEnv :: MetallicModule -> LowerEnv
buildEnv m =
    LowerEnv
        { leConstructors =
            Map.fromList
                [ (mcName c, (mcTag c, length (mcFields c), mcFields c))
                | MAlgebraicType _ cs <- mmTypes m
                , c <- cs
                ]
        , leTypeMap =
            Map.fromList
                [ (ctName td, td)
                | td <- map convertTypeDef (mmTypes m)
                ]
        , leFunctions =
            Map.fromList
                $ [ (mfName f, buildFunctionType f)
                  | f <- mmFunctions m
                  ]
                    ++ [ (methodName, extractMethodType qualTy)
                       | tc <- mmTypeClasses m
                       , (methodName, qualTy) <- mtcMethods tc
                       ]
        }

buildFunctionType :: MetallicFunction -> Type
buildFunctionType mf =
    foldr TArrow (mfReturnType mf) (map snd (mfParams mf))

extractMethodType :: QualifiedType -> Type
extractMethodType (Forall _ _ ty) = ty

-- | Convert a Metal type definition to Circuit
convertTypeDef :: MetallicTypeDef -> CTypeDef
convertTypeDef (MAlgebraicType name cs) =
    CTypeDef
        { ctName = name
        , ctConstructors = map convertConstructor cs
        }
convertTypeDef (MRecordType name fields) =
    CTypeDef
        { ctName = name
        , ctConstructors = [CConstructor name 0 (length fields)]
        }

convertConstructor :: MetallicConstructor -> CConstructor
convertConstructor mc =
    CConstructor
        { ccName = mcName mc
        , ccTag = mcTag mc
        , ccArity = length (mcFields mc)
        }

-- | Lower a complete Metal module to Circuit
lowerModule :: MetallicModule -> CModule
lowerModule m =
    let env = buildEnv m
        functions = evalState (runReaderT (mapM lowerFunction (mmFunctions m)) env) initLowerState
        types = map convertTypeDef (mmTypes m)
        -- collect type class method names as external references
        externalRefs =
            [ methodName
            | tc <- mmTypeClasses m
            , (methodName, _) <- mtcMethods tc
            ]
    in CModule
        { cmName = mmName m
        , cmFunctions = functions
        , cmTypes = types
        , cmIsLinearized = False
        , cmExternalRefs = externalRefs
        }

-- | Lower a Metal function to Circuit
lowerFunction :: MetallicFunction -> LowerM CFunction
lowerFunction mf = do
    body <- lowerExpr (mfBody mf)
    -- For lambda functions with captured variables, extract them from closure_self
    let finalBody = case mfmClosureInfo (mfMetadata mf) of
            Just (ClosureFunctionInfo capturedVars) ->
                -- Wrap body with let bindings that extract captured vars from closure_self
                wrapWithEnvBindings capturedVars body
            Nothing -> body
    pure
        CFunction
            { cfName = mfName mf
            , cfParams = mfParams mf -- Already [(Name, Type)]
            , cfReturnType = mfReturnType mf
            , cfBody = finalBody
            , cfMetadata =
                CFunctionMeta
                    { cfmArity = length (mfParams mf)
                    , cfmIsLinear = False
                    }
            }

{- | Wrap body with let bindings that extract captured variables from closure_self.
For example, if capturedVars = [(x, Int), (y, Bool)]:
  let x = closure_get_env(closure_self, 0) in
  let y = closure_get_env(closure_self, 1) in
  body
-}
wrapWithEnvBindings :: [(String, Type)] -> CTerm -> CTerm
wrapWithEnvBindings capturedVars body =
    foldr wrapOne body (zip [0 ..] capturedVars)
  where
    wrapOne (idx, (varName, varTy)) = CLet varName varTy (CClosureGetEnv (CVar "closure_self" closurePtrType) idx varTy)

-- | Lower a Metal expression to Circuit
lowerExpr :: MetallicExpr -> LowerM CTerm
lowerExpr = \case
    MVar name ty -> do
        env <- ask
        -- Check if this is a nullary constructor
        case Map.lookup name (leConstructors env) of
            Just (tag, 0, _) ->
                -- Nullary constructor: produce CTag with empty fields
                pure $ CTag tag [] ty
            Just _ ->
                -- Constructor with fields: this shouldn't happen as MVar, but treat as a reference to the constructor function
                pure $ CRef name ty
            Nothing ->
                -- Not a constructor: check if it's a top-level function
                if Map.member name (leFunctions env)
                    then pure $ CRef name ty
                    else pure $ CVar name ty
    MLit lit ->
        lowerLiteral lit
    MCall func args resultTy -> do
        -- Check for binary intrinsic pattern: MCall (MVar "+") [a, b]
        case (func, args) of
            (MVar name _, [a, b]) | Just binOp <- lookupBinOp name -> do
                a' <- lowerExpr a
                b' <- lowerExpr b
                pure $ CBinOp binOp a' b'
            (MVar name _, [a, b]) | Just cmpOp <- lookupCmpOp name -> do
                a' <- lowerExpr a
                b' <- lowerExpr b
                pure $ CCmpOp cmpOp a' b'
            (MVar name _, [a]) | Just unaryOp <- lookupUnaryOp name -> do
                a' <- lowerExpr a
                pure $ CUnaryOp unaryOp a'
            _ -> do
                -- Lower function and arguments
                func' <- lowerExpr func
                args' <- mapM lowerExpr args
                -- Build application chain with types
                -- For a chain f x y with result type R, we need intermediate types
                -- f : A -> B -> R, (f x) : B -> R, ((f x) y) : R
                pure $ buildAppChain func' args' resultTy
    MTypeApp expr _ _ ->
        -- Type applications are erased
        lowerExpr expr
    MLet name val body _ -> do
        val' <- lowerExpr val
        body' <- lowerExpr body
        let valTy = getTermType val'
        pure $ CLet name valTy val' body'
    MLambda params body lamTy -> do
        body' <- lowerExpr body
        -- Build nested lambdas with types extracted from the function type
        pure $ buildLamChain params lamTy body'
    MClosure liftedName capturedVars closureTy ->
        -- Closure: a lifted function with captured environment
        pure $ CClosure liftedName capturedVars closureTy
    MConstruct _ctorName tag fields resultTy -> do
        -- Convert to tagged value with all fields
        fields' <- mapM lowerExpr fields
        pure $ CTag tag fields' resultTy
    MArrayLit elems ty -> do
        -- Arrays: encode as tagged value with tag -2 and all elements as fields
        elems' <- mapM lowerExpr elems
        pure $ CTag (-2) elems' ty
    MTuple elems ty -> do
        -- Tuples: encode as tagged value with tag -1 and all elements as fields
        elems' <- mapM lowerExpr elems
        pure $ CTag (-1) elems' ty
    MIf cond thenBr elseBr resultTy -> do
        -- if cond then t else e
        -- Encode as: case cond of { 0 -> e; _ -> t }
        cond' <- lowerExpr cond
        then' <- lowerExpr thenBr
        else' <- lowerExpr elseBr
        -- Use CCase with boolean encoding (False=0, True=1)
        tmp <- freshTmp "cond"
        pure
            $ CLet tmp boolType cond'
            $ CCase
                (CVar tmp boolType)
                [ (0, [], else') -- False case (no fields)
                , (1, [], then') -- True case (no fields)
                ]
                Nothing
                resultTy
    MCase scrutinees arms mdefault resultTy -> do
        case scrutinees of
            [scrut] -> do
                let scrutTy = getMetallicExprType scrut
                -- Check if this is a trivial variable binding pattern (just PVar or PWildcard)
                -- If so, we can avoid the case expression entirely
                case (arms, mdefault) of
                    ([arm], Nothing) | isTrivialPattern (mcaPatterns arm) -> do
                        -- Simple variable binding: let x = scrut in body
                        scrut' <- lowerExpr scrut
                        body' <- lowerExpr (mcaBody arm)
                        case mcaPatterns arm of
                            [PVar name _] -> pure $ CLet name scrutTy scrut' body'
                            [PWildcard _] -> do
                                -- Wildcard: evaluate scrutinee for effects, then body
                                tmp <- freshTmp "wild"
                                pure $ CLet tmp scrutTy scrut' body'
                            _ -> do
                                -- Shouldn't happen due to isTrivialPattern guard
                                tmp <- freshTmp "scrut"
                                arms' <- mapM (lowerCaseArm scrutTy) arms
                                pure $ CLet tmp scrutTy scrut' $ CCase (CVar tmp scrutTy) arms' Nothing resultTy
                    _ -> do
                        -- Real pattern matching needed
                        -- Partition arms into specific patterns (literals, constructors)
                        -- and catch-all patterns (PVar, PWildcard)
                        scrut' <- lowerExpr scrut
                        tmp <- freshTmp "scrut"
                        let (specificArms, catchAllArms) = partitionCaseArms arms
                        arms' <- mapM (lowerCaseArm scrutTy) specificArms
                        -- Use explicit default, or first catch-all arm, or Nothing
                        default' <- case (mdefault, catchAllArms) of
                            (Just def, _) -> Just <$> lowerExpr def
                            (Nothing, firstCatchAll : _) -> do
                                -- For catch-all patterns, bind the variable to scrutinee
                                body' <- lowerExpr (mcaBody firstCatchAll)
                                case mcaPatterns firstCatchAll of
                                    [PVar name _] -> pure $ Just $ CLet name scrutTy (CVar tmp scrutTy) body'
                                    _ -> pure $ Just body'
                            (Nothing, []) -> pure Nothing
                        pure
                            $ CLet tmp scrutTy scrut'
                            $ CCase (CVar tmp scrutTy) arms' default' resultTy
            (scrut : restScrutinees) -> do
                -- Multiple scrutinees: lower to nested cases
                -- case (e1, e2, ...) of { (p1, q1, ...) -> b1; ... }
                -- becomes:
                -- case e1 of { p1 -> case (e2, ...) of { (q1, ...) -> b1; ... }; ... }
                --
                -- Special case: if ALL arms have a catch-all pattern (PVar/PWildcard)
                -- as their first pattern, we don't need a case expression - just bind
                -- the variable and continue with the rest.
                let scrutTy = getMetallicExprType scrut
                scrut' <- lowerExpr scrut

                let firstPatterns = [head (mcaPatterns arm) | arm <- arms, not (null (mcaPatterns arm))]
                    allCatchAll = all isCatchAllPattern firstPatterns

                if allCatchAll && not (null arms)
                    then do
                        -- All first patterns are catch-all (PVar/PWildcard), so we Just bind the variable and continue with nested case!
                        let firstArm = head arms
                            firstPat = head (mcaPatterns firstArm)
                        case firstPat of
                            PVar name _ -> do
                                -- Bind the scrutinee to the variable name
                                let nestedArms = [arm{mcaPatterns = drop 1 (mcaPatterns arm)} | arm <- arms]
                                nestedBody <- lowerExpr (MCase restScrutinees nestedArms mdefault resultTy)
                                pure $ CLet name scrutTy scrut' nestedBody
                            _ -> do
                                -- PWildcard or PAs: just continue without binding
                                let nestedArms = [arm{mcaPatterns = drop 1 (mcaPatterns arm)} | arm <- arms]
                                tmp <- freshTmp "wild"
                                nestedBody <- lowerExpr (MCase restScrutinees nestedArms mdefault resultTy)
                                pure $ CLet tmp scrutTy scrut' nestedBody
                    else do
                        -- Group arms by their first pattern (tag-based grouping)
                        let groupedArms = groupArmsByFirstPattern arms

                        -- Lower each group to a case arm with nested case for remaining scrutinees
                        arms' <- forM groupedArms $ \(firstPat, armsInGroup) -> do
                            (tag, fieldNamesAndTypes) <- extractPatternInfo scrutTy firstPat
                            -- Create the nested case for remaining scrutinees
                            let nestedArms =
                                    [ arm{mcaPatterns = drop 1 (mcaPatterns arm)}
                                    | arm <- armsInGroup
                                    ]
                            nestedBody <- lowerExpr (MCase restScrutinees nestedArms mdefault resultTy)
                            pure (tag, fieldNamesAndTypes, nestedBody)

                        tmp <- freshTmp "scrut"
                        default' <- traverse lowerExpr mdefault
                        pure
                            $ CLet tmp scrutTy scrut'
                            $ CCase (CVar tmp scrutTy) arms' default' resultTy
            [] -> pure CEra
    MFieldAccess expr idx ty -> do
        -- Field access on a tagged value - project the field at the given index
        expr' <- lowerExpr expr
        pure $ CProject expr' idx ty
    MPanic msg ty -> do
        -- Panic: abort execution with the error message
        pure $ CPanic msg ty
    MCompose stmts ty -> do
        -- Monadic composition: lower each statement
        lowerCompose stmts ty

{- | Build an application chain with proper types
Given f : A -> B -> C and args [x : A, y : B], builds ((f x) y) : C
-}
buildAppChain :: CTerm -> [CTerm] -> Type -> CTerm
buildAppChain func [] _ = func
buildAppChain func [arg] resultTy = CApp func arg resultTy
buildAppChain func (arg : args) finalResultTy =
    -- For intermediate applications, we need to compute the intermediate type
    -- f : A -> (B -> C), applying to x : A gives (f x) : B -> C
    let funcTy = getTermType func
        intermediateTy = case funcTy of
            TArrow _ rest -> rest
            _ -> finalResultTy -- fallback
    in buildAppChain (CApp func arg intermediateTy) args finalResultTy

{- | Build a lambda chain with proper types
Given params [x, y] and type A -> B -> C, builds λx:A. λy:B. body
-}
buildLamChain :: [String] -> Type -> CTerm -> CTerm
buildLamChain [] _ body = body
buildLamChain (p : ps) ty body = case ty of
    TArrow paramTy restTy -> CLam p paramTy (buildLamChain ps restTy body)
    _ -> CLam p ty body -- fallback for malformed types

-- | Lower a literal
lowerLiteral :: MetallicLiteral -> LowerM CTerm
lowerLiteral = \case
    MInt i -> pure $ CInt i
    MBool b -> pure $ CBool b
    MString s -> pure $ CStr s

-- | Lower a case arm, given the scrutinee type for field type extraction
lowerCaseArm :: Type -> MCaseArm -> LowerM (Int, [(Name, Type)], CTerm)
lowerCaseArm scrutTy arm = do
    -- Get the pattern (assuming single pattern for now)
    case mcaPatterns arm of
        [pat] -> do
            (tag, fieldNamesAndTypes) <- extractPatternInfo scrutTy pat
            body <- lowerExpr (mcaBody arm)
            pure (tag, fieldNamesAndTypes, body)
        _ -> do
            -- Multiple patterns not yet supported
            body <- lowerExpr (mcaBody arm)
            pure (0, [], body)

{- | Check if a pattern list is trivial (just a single PVar or PWildcard)
Trivial patterns don't need case expressions - they're just variable bindings
-}
isTrivialPattern :: [Pattern] -> Bool
isTrivialPattern [PVar _ _] = True
isTrivialPattern [PWildcard _] = True
isTrivialPattern _ = False

{- | Check if a pattern is a catch-all (variable or wildcard)
These patterns match any value and should become the default case.
-}
isCatchAllPattern :: Pattern -> Bool
isCatchAllPattern (PVar _ _) = True
isCatchAllPattern (PWildcard _) = True
isCatchAllPattern (PAs{}) = True
isCatchAllPattern _ = False

{- | Partition case arms into specific patterns and catch-all patterns.
Specific patterns (literals, constructors) become switch arms.
Catch-all patterns (PVar, PWildcard) become the default case.
-}
partitionCaseArms :: [MCaseArm] -> ([MCaseArm], [MCaseArm])
partitionCaseArms = foldr partition ([], [])
  where
    partition arm (specific, catchAll) =
        case mcaPatterns arm of
            [pat] | isCatchAllPattern pat -> (specific, arm : catchAll)
            _ -> (arm : specific, catchAll)

{- | Extract tag and field names with types from a pattern
The scrutinee type is used to infer field types where possible
-}
extractPatternInfo :: Type -> Pattern -> LowerM (Int, [(Name, Type)])
extractPatternInfo scrutTy = \case
    PConstructor name subPats _ -> do
        env <- ask
        case Map.lookup name (leConstructors env) of
            Just (tag, _, fieldTypes) -> do
                -- Extract names and types from subpatterns, using actual field types
                let typedSubPats = zip (fieldTypes ++ repeat scrutTy) subPats -- fallback to scrutTy if not enough types
                fieldNamesAndTypes <- mapM (uncurry extractFieldNameAndType) typedSubPats
                pure (tag, fieldNamesAndTypes)
            Nothing -> pure (0, []) -- Unknown constructor
    PVar name _ -> pure (0, [(name, scrutTy)])
    PWildcard _ -> pure (0, [])
    PLit lit _ -> case lit of
        LitInt i -> pure (i, [])
        LitBool True -> pure (1, [])
        LitBool False -> pure (0, [])
        LitString _ -> pure (0, [])
    PTuple pats _ -> do
        -- Extract element types from tuple type if possible
        let elemTypes = extractTupleTypes scrutTy
            typedPats = zip (elemTypes ++ repeat scrutTy) pats
        fieldNamesAndTypes <- mapM (uncurry extractFieldNameAndType) typedPats
        pure (-1, fieldNamesAndTypes) -- Tuples use tag -1
    PArray pats _ -> do
        -- Extract element type from array type if possible
        let elemType = extractArrayElemType scrutTy
            typedPats = map (elemType,) pats
        fieldNamesAndTypes <- mapM (uncurry extractFieldNameAndType) typedPats
        pure (-2, fieldNamesAndTypes) -- Arrays use tag -2
    PAs name _ _ -> pure (0, [(name, scrutTy)])

{- | Extract a single field name and type from a pattern.
For simple patterns (PVar, PWildcard), returns the binding name and field type.
For nested patterns (PConstructor, PTuple), returns a temporary name - the
caller is responsible for generating nested match code if needed.

Note: Nested pattern matching is lowered to nested case expressions by the
Metal -> Circuit lowering. This function only needs to handle the binding
extraction for the immediate level.
-}
extractFieldNameAndType :: Type -> Pattern -> LowerM (Name, Type)
extractFieldNameAndType fieldTy = \case
    PVar name _ -> pure (name, fieldTy)
    PWildcard _ -> do
        tmp <- freshTmp "wild"
        pure (tmp, fieldTy)
    PConstructor name _ _ -> do
        -- For nested constructor patterns, bind to a temporary.
        -- The nested match will be handled by a separate case expression
        -- in the pattern compilation (done at Metal level before lowering).
        tmp <- freshTmp ("nested$" ++ name)
        pure (tmp, fieldTy)
    PLit lit _ -> do
        -- Literal patterns: infer type from the literal
        tmp <- freshTmp "lit"
        let litTy = case lit of
                LitInt _ -> intType
                LitBool _ -> boolType
                LitString _ -> TConstructor (TypeConstructor "String" KindStar)
        pure (tmp, litTy)
    PTuple _ _ -> do
        tmp <- freshTmp "tuple"
        pure (tmp, fieldTy)
    PArray _ _ -> do
        tmp <- freshTmp "array"
        pure (tmp, fieldTy)
    PAs name _ _ -> pure (name, fieldTy)

-- | Extract element types from a tuple type
extractTupleTypes :: Type -> [Type]
extractTupleTypes (TApp (TApp (TConstructor tc) t1) t2)
    | tcName tc == "Tuple2" = [t1, t2]
extractTupleTypes (TApp (TApp (TApp (TConstructor tc) t1) t2) t3)
    | tcName tc == "Tuple3" = [t1, t2, t3]
extractTupleTypes _ = [] -- Unknown tuple structure, fall back to empty

-- | Extract element type from an array type
extractArrayElemType :: Type -> Type
extractArrayElemType (TApp (TConstructor tc) elemTy)
    | tcName tc == "Array" = elemTy
extractArrayElemType ty = ty -- Fall back to the original type

-- | Lookup table for binary operators
lookupBinOp :: String -> Maybe BinOp
lookupBinOp name = case name of
    "+" -> Just OpAdd
    "-" -> Just OpSub
    "*" -> Just OpMul
    "/" -> Just OpDiv
    "%" -> Just OpMod
    "&" -> Just OpAnd
    "|" -> Just OpOr
    "^" -> Just OpXor
    _ -> Nothing

-- | Lookup table for comparison operators
lookupCmpOp :: String -> Maybe CmpOp
lookupCmpOp name = case name of
    "==" -> Just OpEq
    "!=" -> Just OpNe
    "<" -> Just OpLt
    "<=" -> Just OpLe
    ">" -> Just OpGt
    ">=" -> Just OpGe
    _ -> Nothing

-- | Lookup table for unary operators
lookupUnaryOp :: String -> Maybe UnaryOp
lookupUnaryOp name = case name of
    "!" -> Just OpNot
    "negate" -> Just OpNeg
    _ -> Nothing

-- | Lower monadic composition
lowerCompose :: [MetallicComposeStmt] -> Type -> LowerM CTerm
lowerCompose [] _ = pure CEra
lowerCompose [MCExpr e] _ = lowerExpr e
lowerCompose (stmt : rest) resultTy = case stmt of
    MCBind name expr -> do
        expr' <- lowerExpr expr
        rest' <- lowerCompose rest resultTy
        let exprTy = getTermType expr'
        -- For strict evaluation, this is just a let binding
        pure $ CLet name exprTy expr' rest'
    MCLet name expr -> do
        expr' <- lowerExpr expr
        rest' <- lowerCompose rest resultTy
        let exprTy = getTermType expr'
        pure $ CLet name exprTy expr' rest'
    MCExpr expr -> do
        expr' <- lowerExpr expr
        rest' <- lowerCompose rest resultTy
        -- Sequence: evaluate expr for effect, continue with rest
        tmp <- freshTmp "seq"
        let exprTy = getTermType expr'
        pure $ CLet tmp exprTy expr' rest'

{- | Group case arms by their first pattern.
Arms with the same first pattern constructor/literal are grouped together.
This is used for multi-scrutinee case lowering to build nested cases.

For example, given arms:
  (A x, B y) -> e1
  (A x, C z) -> e2
  (D w, B y) -> e3

Groups into:
  A -> [(A x, B y) -> e1, (A x, C z) -> e2]
  D -> [(D w, B y) -> e3]
-}
groupArmsByFirstPattern :: [MCaseArm] -> [(Pattern, [MCaseArm])]
groupArmsByFirstPattern =
    -- Use a simple grouping: collect arms with equivalent first patterns
    -- Two patterns are equivalent if they have the same constructor/literal/variable form
    foldr insertArm []
  where
    insertArm :: MCaseArm -> [(Pattern, [MCaseArm])] -> [(Pattern, [MCaseArm])]
    insertArm arm [] = case mcaPatterns arm of
        (p : _) -> [(p, [arm])]
        [] -> []
    insertArm arm ((pat, armsInGroup) : rest) =
        case mcaPatterns arm of
            (p : _)
                | patternsEquivalent p pat ->
                    (pat, arm : armsInGroup) : rest
                | otherwise ->
                    (pat, armsInGroup) : insertArm arm rest
            [] -> (pat, armsInGroup) : rest

{- | Check if two patterns are "equivalent" for grouping purposes.
Two patterns are equivalent if they match the same set of values at the top level.
This means same constructor, same literal, or both are variables/wildcards.
-}
patternsEquivalent :: Pattern -> Pattern -> Bool
patternsEquivalent (PConstructor n1 _ _) (PConstructor n2 _ _) = n1 == n2
patternsEquivalent (PLit l1 _) (PLit l2 _) = l1 == l2
patternsEquivalent (PTuple ps1 _) (PTuple ps2 _) = length ps1 == length ps2
patternsEquivalent (PArray ps1 _) (PArray ps2 _) = length ps1 == length ps2
patternsEquivalent (PVar _ _) (PVar _ _) = True
patternsEquivalent (PWildcard _) (PWildcard _) = True
patternsEquivalent (PVar _ _) (PWildcard _) = True
patternsEquivalent (PWildcard _) (PVar _ _) = True
patternsEquivalent (PAs _ p1 _) p2 = patternsEquivalent p1 p2
patternsEquivalent p1 (PAs _ p2 _) = patternsEquivalent p1 p2
patternsEquivalent _ _ = False
