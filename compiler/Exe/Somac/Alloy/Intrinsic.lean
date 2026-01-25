import Somac.Alloy.Func
import Somac.Alloy.Block

namespace Somac.Alloy.Intrinsic

open Somac.Alloy

/-- Get the closure-compatible signature for a primOp wrapper -/
def primOpSignature (op : PrimOp) : Signature :=
  let name := s!"$intrinsic$$primop_{op.name}"
  match op with
  | .add | .sub | .mul | .div | .mod =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "a", ty := .prim .i32 },
        { id := ⟨2⟩, name := "b", ty := .prim .i32 }
      ]
    , retTy := .prim .i32
    , isClosure := true
    }
  | .eq | .ne | .lt | .le | .gt | .ge =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "a", ty := .prim .i32 },
        { id := ⟨2⟩, name := "b", ty := .prim .i32 }
      ]
    , retTy := .prim .bool
    , isClosure := true
    }
  | .and | .or =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "a", ty := .prim .bool },
        { id := ⟨2⟩, name := "b", ty := .prim .bool }
      ]
    , retTy := .prim .bool
    , isClosure := true
    }
  | .not =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "a", ty := .prim .bool }
      ]
    , retTy := .prim .bool
    , isClosure := true
    }
  | .neg =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "a", ty := .prim .i32 }
      ]
    , retTy := .prim .i32
    , isClosure := true
    }

/-- Get the closure-compatible signature for an intrinsicOp wrapper -/
def intrinsicOpSignature (op : IntrinsicOp) : Signature :=
  let name := s!"$intrinsic$${op.name}"
  match op with
  | .ptrNull =>
    { name
    , params := #[{ id := ⟨0⟩, name := "env", ty := .rawPtr }]
    , retTy := .rawPtr
    , isClosure := true
    }
  | .ptrAdd =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "ptr", ty := .rawPtr },
        { id := ⟨2⟩, name := "offset", ty := .prim .i64 }
      ]
    , retTy := .rawPtr
    , isClosure := true
    }
  | .ptrDiff =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "a", ty := .rawPtr },
        { id := ⟨2⟩, name := "b", ty := .rawPtr }
      ]
    , retTy := .prim .i64
    , isClosure := true
    }
  | .ptrRead =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "ptr", ty := .rawPtr }
      ]
    , retTy := .prim .i64
    , isClosure := true
    }
  | .ptrWrite =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "ptr", ty := .rawPtr },
        { id := ⟨2⟩, name := "val", ty := .prim .i64 }
      ]
    , retTy := .prim .unit
    , isClosure := true
    }
  | .ptrCast =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "ptr", ty := .rawPtr }
      ]
    , retTy := .rawPtr
    , isClosure := true
    }
  | .toCString =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "str", ty := .rawPtr }
      ]
    , retTy := .rawPtr
    , isClosure := true
    }
  | .fromCString =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "cstr", ty := .rawPtr }
      ]
    , retTy := .rawPtr
    , isClosure := true
    }
  | .cstringLen =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "cstr", ty := .rawPtr }
      ]
    , retTy := .prim .u64
    , isClosure := true
    }
  | .strcat =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "a", ty := .rawPtr },
        { id := ⟨2⟩, name := "b", ty := .rawPtr }
      ]
    , retTy := .rawPtr
    , isClosure := true
    }
  | .intToString =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "val", ty := .prim .i32 }
      ]
    , retTy := .rawPtr
    , isClosure := true
    }
  | .pureIO =>
    { name
    , params := #[
        { id := ⟨0⟩, name := "env", ty := .rawPtr },
        { id := ⟨1⟩, name := "val", ty := .prim .i64 }
      ]
    , retTy := .prim .i64
    , isClosure := true
    }

/-- Get signature for an externC wrapper -/
def externCSignature (name : String) (params : Array Ty) (retTy : Ty) : Signature :=
  let wrapperName := s!"$intrinsic$$extern_{name}"
  -- Add env pointer as first param
  let wrapperParams := #[{ id := ⟨0⟩, name := "env", ty := .rawPtr : Param }] ++
    params.mapIdx fun i ty => { id := ⟨i + 1⟩, name := s!"arg{i}", ty }
  { name := wrapperName
  , params := wrapperParams
  , retTy
  , isClosure := true
  }

/-- Convert PrimOp to BinOp for code generation -/
def primOpToBinOp : PrimOp → Option BinOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .div
  | .mod => some .rem
  | .eq => some .eq
  | .ne => some .ne
  | .lt => some .lt
  | .le => some .le
  | .gt => some .gt
  | .ge => some .ge
  | .and => some .and
  | .or => some .or
  | _ => none

/-- Generate wrapper function for a primOp -/
def generatePrimOpWrapper (op : PrimOp) (funcId : FuncId) : Func :=
  let sig := primOpSignature op
  let paramTypes := sig.params.foldl (init := ({} : Std.HashMap Nat Ty)) fun acc p =>
    acc.insert p.id.id p.ty

  -- Build the body based on whether it's binary or unary
  let stmts : Array Stmt :=
    if op.isBinary then
      match primOpToBinOp op with
      | some binOp =>
        let opTy := if op.isComparison then sig.params[1]!.ty else sig.retTy
        #[Stmt.withResult ⟨3⟩ (.binOp binOp (.local ⟨1⟩) (.local ⟨2⟩) opTy)]
      | none => #[]
    else
      match op with
      | .not => #[Stmt.withResult ⟨2⟩ (.unOp .not (.local ⟨1⟩))]
      | .neg => #[Stmt.withResult ⟨2⟩ (.unOp .neg (.local ⟨1⟩))]
      | _ => #[]

  let resultLocal := if op.isBinary then ⟨3⟩ else ⟨2⟩
  let terminator := Terminator.ret (.local resultLocal)

  let entryBlock : Block :=
    { id := .entry
    , stmts := stmts
    , terminator := terminator
    }

  let cfg := CFG.withEntry entryBlock

  { id := funcId
  , sig := sig
  , body := some cfg
  , nextLocalId := if op.isBinary then 4 else 3
  , localTypes := paramTypes.insert resultLocal.id sig.retTy
  }

/-- Generate wrapper function for an intrinsicOp -/
def generateIntrinsicOpWrapper (op : IntrinsicOp) (funcId : FuncId) : Func :=
  let sig := intrinsicOpSignature op
  let paramTypes := sig.params.foldl (init := ({} : Std.HashMap Nat Ty)) fun acc p =>
    acc.insert p.id.id p.ty

  -- Build args array (skip env at position 0)
  let args : Array Operand := sig.params.toList.drop 1 |>.toArray.map fun p => .local p.id

  let (stmts, resultLocal, nextLocal) : Array Stmt × LocalId × Nat :=
    if op.hasResult then
      let resultId : LocalId := ⟨sig.params.size⟩
      (#[Stmt.withResult resultId (.callIntrinsic op args sig.retTy)], resultId, sig.params.size + 1)
    else
      (#[Stmt.void (.callIntrinsic op args sig.retTy)], ⟨0⟩, sig.params.size)

  let terminator :=
    if op.hasResult then Terminator.ret (.local resultLocal)
    else Terminator.retUnit

  let entryBlock : Block :=
    { id := .entry
    , stmts := stmts
    , terminator := terminator
    }

  let cfg := CFG.withEntry entryBlock

  { id := funcId
  , sig := sig
  , body := some cfg
  , nextLocalId := nextLocal
  , localTypes := if op.hasResult then paramTypes.insert resultLocal.id sig.retTy else paramTypes
  }

/-- Generate wrapper function for an externC function -/
def generateExternCWrapper (name : String) (paramTys : Array Ty) (retTy : Ty) (funcId : FuncId) : Func :=
  let sig := externCSignature name paramTys retTy
  let paramTypes := sig.params.foldl (init := ({} : Std.HashMap Nat Ty)) fun acc p =>
    acc.insert p.id.id p.ty

  -- Build args array (skip env at position 0)
  let args : Array Operand := sig.params.toList.drop 1 |>.toArray.map fun p => .local p.id

  let resultId : LocalId := ⟨sig.params.size⟩
  let stmts := #[Stmt.withResult resultId (.callExtern name args retTy)]

  let terminator := Terminator.ret (.local resultId)

  let entryBlock : Block :=
    { id := .entry
    , stmts := stmts
    , terminator := terminator
    }

  let cfg := CFG.withEntry entryBlock

  { id := funcId
  , sig := sig
  , body := some cfg
  , nextLocalId := sig.params.size + 1
  , localTypes := paramTypes.insert resultId.id retTy
  }

/-- Information about a FuncRef that needs a wrapper -/
inductive WrapperNeeded where
  | primOp (op : PrimOp)
  | intrinsicOp (op : IntrinsicOp)
  | externC (name : String)
  deriving Repr, BEq, Hashable

/-- Collect all FuncRefs needing wrappers from a module -/
def collectWrappersNeeded (mod : Module) : Std.HashSet WrapperNeeded := Id.run do
  let mut result : Std.HashSet WrapperNeeded := {}

  for func in mod.funcs do
    if let some cfg := func.body then
      for block in cfg.allBlocks do
        for stmt in block.stmts do
          match stmt.inst with
          | .makeClosure funcRef _ | .makeClosurePoly funcRef _ _ =>
            match funcRef with
            | .primOp op => result := result.insert (.primOp op)
            | .intrinsic op => result := result.insert (.intrinsicOp op)
            | .externC name => result := result.insert (.externC name)
            | _ => pure ()
          | _ => pure ()

  result

/-- Generate a wrapper function for a WrapperNeeded -/
def generateWrapper (needed : WrapperNeeded) (funcId : FuncId) : Func :=
  match needed with
  | .primOp op => generatePrimOpWrapper op funcId
  | .intrinsicOp op => generateIntrinsicOpWrapper op funcId
  | .externC name => generateExternCWrapper name #[.prim .i64] (.prim .i64) funcId

/-- Get the wrapper name for a WrapperNeeded -/
def wrapperName : WrapperNeeded → String
  | .primOp op => s!"$intrinsic$$primop_{op.name}"
  | .intrinsicOp op => s!"$intrinsic$${op.name}"
  | .externC name => s!"$intrinsic$$extern_{name}"

end Somac.Alloy.Intrinsic
