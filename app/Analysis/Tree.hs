{-# LANGUAGE MultiParamTypeClasses #-}
module Analysis.Tree where

import Data.Map as Map
import Data.Set as Set
import Control.Monad.State
import Control.Monad.Except
import Parsing.Tree (Expression(..))

import Parsing.Type

data TypeScheme
    = STypeLiteral Type
    | STypeVar Int
    | STypeLambda TypeScheme TypeScheme

newtype InferM a = InferM {
    runInfer :: ExceptT String (State InferState) a
}

instance Functor InferM where
    fmap f m = InferM $ fmap f (runInfer m)

instance Applicative InferM where
    pure x = InferM $ pure x
    f <*> x = InferM $ runInfer f <*> runInfer x

instance Monad InferM where
    m >>= k = InferM $ runInfer m >>= runInfer . k

instance MonadState InferState InferM where
    get = InferM get
    put = InferM . put

type Substitution = Map.Map Int TypeScheme

class Substitutable a where
    free :: a -> Set.Set Int
    apply :: Substitution -> a -> a

instance Substitutable TypeScheme where
    free (STypeLiteral _) = Set.empty
    free (STypeVar v) = Set.singleton v
    free (STypeLambda t1 t2) = free t1 `Set.union` free t2

    apply _ t@(STypeLiteral _) = t
    apply s (STypeVar v) = Map.findWithDefault (STypeVar v) v s
    apply s (STypeLambda t1 t2) = STypeLambda (apply s t1) (apply s t2)

fresh :: InferM TypeScheme
fresh = do
    st <- get
    put $ st { inferNextVar = inferNextVar st + 1 }
    return $ STypeVar $ inferNextVar st

data InferState = InferState
  { inferNextVar :: Int
  , inferTypeMap :: Map.Map Expression Type
  }
