module Analysis.Errors where
import Parsing.Tree (Expression)

data AnalysisError 
    = UnificationError Expression