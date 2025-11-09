module Metal.Gen.Extracts where

import Data.Map (Map)
import qualified Data.Map as Map
import Metal.Function (MetallicFunction)
import Metal.Module (MetallicInstance (..))
import Typing.Types

groupInstanceMethods :: Map (String, Type, String) MetallicFunction -> [MetallicInstance]
groupInstanceMethods methodMap =
    Map.elems
        $ Map.fromListWith
            ( \(MetallicInstance cn it ms1) (MetallicInstance _ _ ms2) ->
                MetallicInstance cn it (ms1 ++ ms2)
            )
            [ (key, MetallicInstance className instanceType [method])
            | ((className, instanceType, _), method) <- Map.toList methodMap
            , let key = (className, instanceType)
            ]
