module Project.Module where
import Parsing.Type (Type)

data SomaModule = SomaModule
    { moduleName :: String
    , moduleFunctions :: [ModuleFunction]
    }

data ModuleFunction = ModuleFunction
    { moduleFunctionName :: String
    , moduleFunctionReturnType :: Type
    , moduleFunctionParameters :: [Type]
    }