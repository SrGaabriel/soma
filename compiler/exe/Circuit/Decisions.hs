{-# LANGUAGE RecordWildCards #-}

module Circuit.Decisions where

import Data.List (groupBy, nub, partition, sortOn)
import qualified Data.Map.Strict as Map
import Project.Name (Name)
import Syntax.Patterns (Literal (..), Pattern (..), ResolvedPattern)

type Action = Int

type Var = String

data Accessor
    = Root Int
    | Field Accessor Int
    | TupleElem Accessor Int
    | ArrayElem Accessor Int
    deriving (Show, Eq, Ord)

data MatrixRow = MatrixRow
    { rowPatterns :: [ResolvedPattern]
    , rowAction :: Action
    }
    deriving (Show, Eq)

data PatternMatrix = PatternMatrix
    { matrixRows :: [MatrixRow]
    , matrixVars :: [Accessor]
    }
    deriving (Show, Eq)

mkPatternMatrix :: [([ResolvedPattern], Action)] -> PatternMatrix
mkPatternMatrix [] = PatternMatrix{matrixRows = [], matrixVars = []}
mkPatternMatrix clauses@((pats, _) : _) =
    let numArgs = length pats
        rows = [MatrixRow p act | (p, act) <- clauses]
        vars = [Root i | i <- [0 .. numArgs - 1]]
    in PatternMatrix{matrixRows = rows, matrixVars = vars}

isEmptyMatrix :: PatternMatrix -> Bool
isEmptyMatrix = null . matrixRows

hasNoColumns :: PatternMatrix -> Bool
hasNoColumns = null . matrixVars

data DecisionTree
    = Leaf Action
    | Fail
    | Switch Accessor [(Constructor, DecisionTree)] (Maybe DecisionTree)
    | Guard Accessor DecisionTree DecisionTree
    deriving (Show, Eq)

data Constructor
    = LitCtor Literal
    | DataCtor Name Int
    | TupleCtor Int
    | ArrayCtor Int
    | ConsCtor
    deriving (Show, Eq, Ord)

compile :: PatternMatrix -> DecisionTree
compile matrix@PatternMatrix{..}
    | isEmptyMatrix matrix = Fail
    | hasNoColumns matrix =
        case matrixRows of
            [] -> Fail
            (r : _) -> Leaf (rowAction r)
    | otherwise =
        let col = chooseColumn matrix
        in compileColumn col matrix

chooseColumn :: PatternMatrix -> Int
chooseColumn _matrix = 0

compileColumn :: Int -> PatternMatrix -> DecisionTree
compileColumn col matrix@PatternMatrix{..} =
    let accessor = matrixVars !! col
        (ctorRows, defaultRows) = partitionRows col matrixRows
    in if null ctorRows
        then compileDefault col accessor matrix defaultRows
        else compileSwitch col accessor matrix ctorRows defaultRows

partitionRows :: Int -> [MatrixRow] -> ([(Constructor, [MatrixRow])], [MatrixRow])
partitionRows col rows =
    let (defaults, ctors) = partition (isDefaultPattern . (!! col) . rowPatterns) rows
        groupedCtors = groupByConstructor col ctors
    in (groupedCtors, defaults)

isDefaultPattern :: ResolvedPattern -> Bool
isDefaultPattern PVar{} = True
isDefaultPattern PWildcard{} = True
isDefaultPattern PAs{} = True
isDefaultPattern _ = False

groupByConstructor :: Int -> [MatrixRow] -> [(Constructor, [MatrixRow])]
groupByConstructor col rows =
    let sorted = sortOn (patternConstructor . (!! col) . rowPatterns) rows
        grouped =
            groupBy
                ( \r1 r2 ->
                    patternConstructor (rowPatterns r1 !! col)
                        == patternConstructor (rowPatterns r2 !! col)
                )
                sorted
    in [(patternConstructor $ rowPatterns r !! col, g) | g@(r : _) <- grouped]

patternConstructor :: ResolvedPattern -> Constructor
patternConstructor (PLit lit _) = LitCtor lit
patternConstructor (PConstructor name pats _) = DataCtor name (length pats)
patternConstructor (PTuple pats _) = TupleCtor (length pats)
patternConstructor (PArray pats _) = ArrayCtor (length pats)
patternConstructor (PCons _ _ _) = ConsCtor
patternConstructor (PAs _ pat _) = patternConstructor pat
patternConstructor _ = error "Not a constructor pattern"

compileDefault :: Int -> Accessor -> PatternMatrix -> [MatrixRow] -> DecisionTree
compileDefault col _accessor matrix defaultRows =
    let newMatrix = specializeDefault col matrix defaultRows
    in compile newMatrix

compileSwitch ::
    Int ->
    Accessor ->
    PatternMatrix ->
    [(Constructor, [MatrixRow])] ->
    [MatrixRow] ->
    DecisionTree
compileSwitch col accessor matrix ctorGroups defaultRows =
    let branches =
            [ (ctor, compile (specializeConstructor col ctor matrix (rows ++ defaultRows)))
            | (ctor, rows) <- ctorGroups
            ]
        defaultCase =
            if null defaultRows
                then Nothing
                else Just (compile (specializeDefault col matrix defaultRows))
    in Switch accessor branches defaultCase

specializeConstructor :: Int -> Constructor -> PatternMatrix -> [MatrixRow] -> PatternMatrix
specializeConstructor col ctor PatternMatrix{..} rows =
    let arity = constructorArity ctor
        accessor = matrixVars !! col
        newVars = [Field accessor i | i <- [0 .. arity - 1]]
        allVars = take col matrixVars ++ newVars ++ drop (col + 1) matrixVars
        newRows = [specializeRow col ctor row | row <- rows]
    in PatternMatrix{matrixRows = newRows, matrixVars = allVars}

constructorArity :: Constructor -> Int
constructorArity (LitCtor _) = 0
constructorArity (DataCtor _ n) = n
constructorArity (TupleCtor n) = n
constructorArity (ArrayCtor n) = n
constructorArity ConsCtor = 2

specializeRow :: Int -> Constructor -> MatrixRow -> MatrixRow
specializeRow col ctor row =
    let pats = rowPatterns row
        pat = pats !! col
        newPats = case pat of
            PConstructor _ subPats _ -> subPats
            PTuple subPats _ -> subPats
            PArray subPats _ -> subPats
            PCons h t _ -> [h, t]
            PLit{} -> []
            PAs _ p _ -> extractSubPatterns p
            PVar _ s -> replicate (constructorArity ctor) (PWildcard s)
            PWildcard s -> replicate (constructorArity ctor) (PWildcard s)
        allPats = take col pats ++ newPats ++ drop (col + 1) pats
    in MatrixRow allPats (rowAction row)

extractSubPatterns :: ResolvedPattern -> [ResolvedPattern]
extractSubPatterns (PConstructor _ pats _) = pats
extractSubPatterns (PTuple pats _) = pats
extractSubPatterns (PArray pats _) = pats
extractSubPatterns (PCons h t _) = [h, t]
extractSubPatterns PLit{} = []
extractSubPatterns (PAs _ p _) = extractSubPatterns p
extractSubPatterns PWildcard{} = []
extractSubPatterns PVar{} = []

specializeDefault :: Int -> PatternMatrix -> [MatrixRow] -> PatternMatrix
specializeDefault col PatternMatrix{..} rows =
    let newVars = take col matrixVars ++ drop (col + 1) matrixVars
        newRows =
            [ MatrixRow
                (take col (rowPatterns row) ++ drop (col + 1) (rowPatterns row))
                (rowAction row)
            | row <- rows
            ]
    in PatternMatrix{matrixRows = newRows, matrixVars = newVars}

data DecisionDAG
    = DAGLeaf Action
    | DAGFail
    | DAGSwitch Accessor [(Constructor, NodeId)] (Maybe NodeId)
    deriving (Show, Eq, Ord)

type NodeId = Int

data DAG = DAG
    { dagNodes :: Map.Map NodeId DecisionDAG
    , dagRoot :: NodeId
    , dagNextId :: NodeId
    }
    deriving (Show, Eq)

buildDAG :: DecisionTree -> DAG
buildDAG tree =
    let initDag = DAG{dagNodes = Map.empty, dagRoot = 0, dagNextId = 0}
        (rootId, dag) = buildDAGHelper tree initDag
    in dag{dagRoot = rootId}

buildDAGHelper :: DecisionTree -> DAG -> (NodeId, DAG)
buildDAGHelper tree dag =
    case tree of
        Fail ->
            let nodeId = dagNextId dag
                node = DAGFail
                newDag = dag{dagNodes = Map.insert nodeId node (dagNodes dag), dagNextId = nodeId + 1}
            in (nodeId, newDag)
        Leaf action ->
            let nodeId = dagNextId dag
                node = DAGLeaf action
                newDag = dag{dagNodes = Map.insert nodeId node (dagNodes dag), dagNextId = nodeId + 1}
            in (nodeId, newDag)
        Switch accessor branches defaultCase ->
            let (branchIds, dag1) =
                    foldl
                        ( \(ids, d) (ctor, subtree) ->
                            let (subId, d') = buildDAGHelper subtree d
                            in (ids ++ [(ctor, subId)], d')
                        )
                        ([], dag)
                        branches
                (defaultId, dag2) = case defaultCase of
                    Nothing -> (Nothing, dag1)
                    Just dt ->
                        let (subId, d') = buildDAGHelper dt dag1
                        in (Just subId, d')
                nodeId = dagNextId dag2
                node = DAGSwitch accessor branchIds defaultId
                newNodes = Map.insert nodeId node (dagNodes dag2)
                newDag = dag2{dagNodes = newNodes, dagNextId = nodeId + 1}
            in (nodeId, newDag)
        Guard _accessor _thenTree elseTree ->
            buildDAGHelper elseTree dag

optimizeDAG :: DAG -> DAG
optimizeDAG dag =
    let nodes = Map.toList (dagNodes dag)
        sharedNodes =
            Map.fromList
                [ (minimum [nid' | (nid', n') <- nodes, n' == node], node)
                | node <- nub (map snd nodes)
                ]
    in dag{dagNodes = sharedNodes}

prettyTree :: DecisionTree -> String
prettyTree = prettyTreeIndent 0
  where
    prettyTreeIndent indent tree =
        let ind = replicate (indent * 2) ' '
        in case tree of
            Leaf action -> ind ++ "Leaf " ++ show action
            Fail -> ind ++ "Fail"
            Switch acc branches def ->
                ind
                    ++ "Switch "
                    ++ show acc
                    ++ "\n"
                    ++ unlines
                        [ ind
                            ++ "  "
                            ++ show ctor
                            ++ " ->\n"
                            ++ prettyTreeIndent (indent + 2) subtree
                        | (ctor, subtree) <- branches
                        ]
                    ++ case def of
                        Nothing -> ""
                        Just dt -> ind ++ "  default ->\n" ++ prettyTreeIndent (indent + 2) dt
            Guard acc t1 t2 ->
                ind
                    ++ "Guard "
                    ++ show acc
                    ++ "\n"
                    ++ ind
                    ++ "  then:\n"
                    ++ prettyTreeIndent (indent + 2) t1
                    ++ "\n"
                    ++ ind
                    ++ "  else:\n"
                    ++ prettyTreeIndent (indent + 2) t2

prettyDAG :: DAG -> String
prettyDAG dag =
    "DAG (root: "
        ++ show (dagRoot dag)
        ++ ")\n"
        ++ unlines [show nid ++ ": " ++ show node | (nid, node) <- Map.toList (dagNodes dag)]

compilePatterns :: [([ResolvedPattern], Action)] -> DecisionTree
compilePatterns clauses = compile (mkPatternMatrix clauses)

compilePatternsToDAG :: [([ResolvedPattern], Action)] -> DAG
compilePatternsToDAG clauses =
    buildDAG $ compilePatterns clauses
