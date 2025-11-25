{-# LANGUAGE NamedFieldPuns #-}

module Metal.Gen.Unique where

import Control.Monad.State (gets, modify)
import qualified Data.Map as Map
import Metal.Gen.Core (MetalGen, MetalGenState (metalUniques))
import Project.Symbols (Symbol (..))

distinguish :: Symbol -> MetalGen String
distinguish s@ResolvedSymbol{resolvedSymbolName} = do
    uniques <- gets metalUniques
    unique <- case Map.lookup s uniques of
        Just n -> pure $ show n
        Nothing -> do
            let n = Map.size uniques
            modify $ \st -> st{metalUniques = Map.insert s n uniques}
            pure $ show n
    pure $ resolvedSymbolName ++ "#" ++ unique

    
-- todo: implement proper sanitization
sanitizeName :: String -> String
sanitizeName a = a