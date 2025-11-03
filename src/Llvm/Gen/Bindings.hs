module Llvm.Gen.Bindings where

import Control.Monad (when)
import Control.Monad.RWS
import qualified Data.Map as Map
import Llvm.Gen.Core (IrGen, IrGenState (..))
import Llvm.Gen.Functions (compileFunction)
import Llvm.Gen.Metadata (PolymorphicFunctionMetadata (..))
import Llvm.Gen.Value (compileValue)
import Syntax.Tree (Expr (..))
import Typing.Types (QualifiedType (Forall), isPolymorphic)

compileBindingDef :: Expr -> IrGen ()
compileBindingDef (ExprBindingDef name qualType@(Forall _ constraints bindingTyp) body _ _) = do
    when (isPolymorphic bindingTyp || not (null constraints)) $ do
        let polyFunc =
                PolymorphicFunction
                    { polyFuncName = name
                    , polyFuncType = qualType
                    , polyFuncBody = body
                    }
        modify $ \s -> s{polymorphicFunctions = Map.insert name polyFunc (polymorphicFunctions s)}
    when (null constraints)
        $ compileFunction name bindingTyp body compileValue
compileBindingDef _ = error "Unsupported binding definition expression"
