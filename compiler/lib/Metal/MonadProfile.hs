{-# LANGUAGE NamedFieldPuns #-}

-- Motivation:
-- - We want to eliminate monadic structure by lowering based on semantic shape,
--   not stringly-typed names like Some/None or Left/Right.
-- - A "profile" captures the operational behavior of a monad family so
--   lowering/codegen can act uniformly on any ADT that matches the shape.
--
-- Current inference (purely from ADT shapes):
-- - Short-circuit profiles:
--   * Option-like: exactly two constructors; one has arity 0 (fail), the other arity 1 (success).
--   * Either-like: exactly two constructors; both have arity 1. We assume a right-biased monad
--     for performance/usability and choose the constructor with the highest tag as success.
module Metal.MonadProfile (
    MonadProfile (..),
    MonadProfiles (..),
    buildMonadProfiles,
    lookupProfile,
    isShortCircuit,
    shortCircuitCtors,
) where

import Data.List (sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Metal.Module (
    MetallicConstructor (..),
    MetallicModule (..),
    MetallicTypeDef (..),
 )
import Project.Name (Name)
import Utils.Lists (hardHead)

data MonadProfile
    = ProfileShortCircuit
        { mpTypeName :: Name
        , mpSuccessCtor :: Name
        , mpFailCtor :: Name
        }
    | ProfileStateLike
        { mpTypeName :: Name
        }
    | ProfileReaderLike
        { mpTypeName :: Name
        }
    | ProfileIOLike
        { mpTypeName :: Name
        }
    | ProfileListLike
        { mpTypeName :: Name
        , mpLazy :: Bool
        }
    deriving (Show, Eq)

newtype MonadProfiles = MonadProfiles
    { mpByTypeName :: Map Name MonadProfile
    }
    deriving (Show, Eq)

lookupProfile :: MonadProfiles -> Name -> Maybe MonadProfile
lookupProfile (MonadProfiles m) tn = Map.lookup tn m

isShortCircuit :: MonadProfile -> Bool
isShortCircuit ProfileShortCircuit{} = True
isShortCircuit _ = False

shortCircuitCtors :: MonadProfile -> Maybe (Name, Name)
shortCircuitCtors ProfileShortCircuit{mpSuccessCtor, mpFailCtor} = Just (mpSuccessCtor, mpFailCtor)
shortCircuitCtors _ = Nothing

buildMonadProfiles :: MetallicModule -> MonadProfiles
buildMonadProfiles MetallicModule{mmTypes} =
    let pairs = concatMap inferFromType mmTypes
    in MonadProfiles (Map.fromList pairs)

inferFromType :: MetallicTypeDef -> [(Name, MonadProfile)]
inferFromType (MAlgebraicType{mtName, mtConstructors}) =
    case mtConstructors of
        [c0, c1] ->
            case (arity c0, arity c1) of
                (0, 1) ->
                    [
                        ( mtName
                        , ProfileShortCircuit
                            { mpTypeName = mtName
                            , mpSuccessCtor = mcName c1
                            , mpFailCtor = mcName c0
                            }
                        )
                    ]
                (1, 0) ->
                    [
                        ( mtName
                        , ProfileShortCircuit
                            { mpTypeName = mtName
                            , mpSuccessCtor = mcName c0
                            , mpFailCtor = mcName c1
                            }
                        )
                    ]
                (1, 1) ->
                    let ordered = sortOn mcTag [c0, c1]
                        failC = hardHead ordered
                        succC = last ordered
                    in [
                           ( mtName
                           , ProfileShortCircuit
                                { mpTypeName = mtName
                                , mpSuccessCtor = mcName succC
                                , mpFailCtor = mcName failC
                                }
                           )
                       ]
                _ -> []
        _ -> []
  where
    arity :: MetallicConstructor -> Int
    arity = length . mcFields
inferFromType _ = []
