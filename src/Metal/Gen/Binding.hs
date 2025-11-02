module Metal.Gen.Binding where
import Syntax.Tree (Expr (..))
import Metal.Gen.Core (MetalGen, addFunction)
import Metal.Gen.Value (metallizeValue)
import Typing.Types
import Metal.Function
import Typing.Currying (uncurryFunction)
import Metal.Gen.Extracts (extractParamNames)

metallizeBinding :: Expr -> MetalGen ()
metallizeBinding (ExprBindingDef name (Forall typeVars constraints bindingTyp) body _ _) = do
    metalBody <- metallizeValue body
    
    let (paramTypes, retType) = uncurryFunction bindingTyp
    
    let paramNames = extractParamNames body (length paramTypes)
    let params = zip paramNames paramTypes
    
    let func = if null typeVars && null constraints
        then 
            MMonomorphic
                { mfName = name
                , mfParams = params
                , mfReturnType = retType
                , mfBody = metalBody
                }
        else 
            MPolymorphic
                { mfName = name
                , mfTypeParams = typeVars
                , mfConstraints = constraints
                , mfParams = params
                , mfReturnType = retType
                , mfBody = metalBody
                }
    
    addFunction name func
metallizeBinding _ = return ()