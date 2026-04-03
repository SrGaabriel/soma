import Somac.Alloy.Types
import Somac.Alloy.Inst
import Somac.Alloy.Block
import Somac.Alloy.Func
import Somac.Alloy.Lower
import Somac.Alloy.Pretty
import Somac.Alloy.Monomorphize
import Somac.Alloy.Analysis
import Somac.Alloy.DefUse
import Somac.Alloy.ClosureSpec
import Somac.Alloy.Borrow
import Somac.Alloy.Merge
import Somac.Alloy.Serialize
import Somac.Alloy.Reuse
import Somac.Alloy.TailCall
import Somac.Alloy.AccumIntro
import Somac.Alloy.ArithAccum
import Somac.Alloy.ListIntrinsics
import Somac.Alloy.IOIntrinsics
import Somac.Alloy.ElemSize
import Somac.Alloy.ConsInline

namespace Somac.Alloy

export Lower (lower lowerGraph buildWiredFuncRegistry)
export Pretty (pp ppColored ppFn ppBb ppModule)
export Monomorphize (monomorphize isFullyMonomorphic reportPolymorphism)
export ClosureSpec (closureSpec)
export TailCall (tailCallOpt mutualTailCallOpt)
export AccumIntro (accumIntro)
export ArithAccum (arithAccumIntro)
export ListIntrinsics (replaceListIntrinsics)
export IOIntrinsics (replaceIOIntrinsics)
export ElemSize (refineElemSizes)
export ConsInline (inlineConsFastPath)
export Borrow (borrowModule BorrowStats)
export Reuse (reuseModule)
export Merge (merge mergeModules)
export Serialize (serializeModule deserializeModule writeAlloyBin readAlloyBin)

end Somac.Alloy
