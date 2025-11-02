{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Metal.Gen.Patterns where

import qualified Data.Map as Map
import Decisions.Model
import Metal.Expr
import Typing.Types

metallizeDag :: MetallicExpr -> DAG -> [MetallicExpr] -> Type -> MetallicExpr
metallizeDag scrutinee dag = metallizeDagNode scrutinee dag (dagRoot dag)

metallizeDagNode :: MetallicExpr -> DAG -> NodeId -> [MetallicExpr] -> Type -> MetallicExpr
metallizeDagNode scrutinee dag nodeId bodies resultTy =
    let Just node = Map.lookup nodeId (dagNodes dag)
    in case node of
        DAGLeaf action ->
            bodies !! action
        DAGFail ->
            MPanic "Pattern match failure" resultTy
        DAGSwitch accessor branches defaultCase ->
            let metalAccessor = accessorToMetallic scrutinee accessor
                metalBranches =
                    [ (ctor, metallizeDagNode scrutinee dag targetId bodies resultTy)
                    | (ctor, targetId) <- branches
                    ]
                metalDefault =
                    fmap
                        (\defId -> metallizeDagNode scrutinee dag defId bodies resultTy)
                        defaultCase
            in MSwitch metalAccessor metalBranches metalDefault resultTy

accessorToMetallic :: MetallicExpr -> Accessor -> MetallicExpr
accessorToMetallic base (Root _n) = base
accessorToMetallic base (Field accessor fieldIdx) =
    let baseAccess = accessorToMetallic base accessor
        ty = getMetallicExprType baseAccess
    in MFieldAccess baseAccess fieldIdx ty
accessorToMetallic _base _accessor = error "TODO: other accessors"
