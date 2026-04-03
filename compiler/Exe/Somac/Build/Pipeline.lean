import Soma.Project.Metadata
import Soma.Project
import Soma.Project.Check
import Soma.Core.LambdaLift
import Soma.Driver.Target
import Somac.Circuit
import Somac.Alloy
import Somac.Alloy.Merge
import Somac.Alloy.Serialize
import Somac.Llvm

namespace Somac.Build

open Soma
open Soma.Project
open Soma.Syntax

open Soma.Project.Check

/-- Load external dependencies from metadata JSON files -/
def loadExternalDependencies (deps : Array (String × System.FilePath))
    : IO (Except CheckError (Array ExternalDependency)) :=
  if deps.isEmpty then
    pure (.ok #[])
  else
    Metadata.loadMetadataFiles deps

/-- Load Alloy IR modules from a .toria package file -/
def loadAlloyModulesFromToria (path : System.FilePath) : IO (Except String (Array (String × Alloy.Module))) := do
  let tmpDir := path.withExtension "alloy.extract.tmp"
  IO.FS.createDirAll tmpDir

  let result ← IO.Process.output {
    cmd := "tar"
    args := #["-xzf", path.toString, "-C", tmpDir.toString]
  }

  if result.exitCode != 0 then
    IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
    return .error s!"Failed to extract tarball: {result.stderr}"

  let entries ← tmpDir.readDir
  let extractedDir := match entries.toList.head? with
    | some entry => tmpDir / entry.fileName
    | none => tmpDir

  -- Read manifest to get module names
  let manifestPath := extractedDir / "manifest.bin"
  let manifestBytes ← IO.FS.readBinFile manifestPath

  -- The manifest format is: magic (4 bytes) + serialized PackageManifest
  let manifestMagic : ByteArray := ByteArray.mk #[0x54, 0x4F, 0x52, 0x49] -- "TORI"
  if manifestBytes.size < 4 then
    IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
    return .error "Invalid manifest: too small"

  let magic := ByteArray.mk (manifestBytes.toList.take 4).toArray
  if magic != manifestMagic then
    IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
    return .error "Invalid manifest: bad magic bytes"

  let alloyDir := extractedDir / "alloy"
  let mut alloyModules : Array (String × Alloy.Module) := #[]

  if ← alloyDir.pathExists then
    let packageDirs ← alloyDir.readDir
    for packageEntry in packageDirs do
      let packageDir := alloyDir / packageEntry.fileName
      if ← packageDir.isDir then
        let moduleEntries ← packageDir.readDir
        for entry in moduleEntries do
          if entry.fileName.endsWith ".alloybin" then
            let modName := s!"{packageEntry.fileName}/{entry.fileName.dropEnd 9}" -- "package/module"
            let binPath := packageDir / entry.fileName
            match ← Alloy.Serialize.readAlloyBin binPath with
            | .ok alloyMod => alloyModules := alloyModules.push (modName, alloyMod)
            | .error e =>
              IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
              return .error s!"Failed to read Alloy module '{modName}': {e}"

  IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
  pure (.ok alloyModules)

/-- Load Alloy IR from all dependency .toria files -/
def loadDependencyAlloyModules (deps : Array (String × System.FilePath))
    : IO (Except String (Array (String × Alloy.Module))) := do
  if deps.isEmpty then
    pure (.ok #[])
  else
    let mut allModules : Array (String × Alloy.Module) := #[]
    for (depName, path) in deps do
      match path.extension with
      | some "toria" =>
        match ← loadAlloyModulesFromToria path with
        | .ok modules =>
          IO.println s!"  Loaded {modules.size} Alloy module(s) from dependency '{depName}'"
          allModules := allModules ++ modules
        | .error e =>
          return .error s!"Failed to load Alloy IR from '{depName}': {e}"
      | _ => pure ()
    pure (.ok allModules)

/-- Lower a single checked module to Alloy IR -/
def lowerToAlloy (cm : CheckedModule) (globals : Soma.Dependent.Globals) : IO Alloy.Module := do
  -- Lambda lifting
  let liftedTypedFunctions := Soma.Core.LambdaLift.liftAll cm.typedFunctions cm.name cm.uniqueNextId (globals.toGlobalEnvWithClasses cm.instanceEnv) (Somac.Circuit.Lower.unfoldValue · cm.abbrevEnv)

  -- Lower to Circuit IR
  let graph := Circuit.Lower.lower cm.untypedModule.types liftedTypedFunctions cm.usages (some globals) cm.instanceEnv (metas := cm.metas) (abbrevEnv := cm.abbrevEnv)

  -- Partial evaluation
  let (optimized, _stats) ← Circuit.partialEval graph

  -- Lower to Alloy MIR
  let primTypes := Alloy.Lower.buildPrimTypeRegistry globals.wiredIn
  let wiredFuncs := Alloy.Lower.buildWiredFuncRegistry globals.wiredIn
  let erasure : Alloy.Lower.ErasureCtx := {
    worldUid? := globals.wiredIn.getUnique? .typeWorld |>.map (·.name.id.id)
    pairUid? := globals.wiredIn.getUnique? .typePair |>.map (·.name.id.id)
  }
  let alloyMod := Alloy.Lower.lower optimized cm.name primTypes globals.inductives globals.intrinsics wiredFuncs (abbrevEnv := cm.abbrevEnv) (metaState := cm.metas) (erasure := erasure)
  return alloyMod

/-- Result of compilation pipeline -/
structure CompileResult where
  /-- Generated LLVM IR -/
  llvmIR : Option String := none
  /-- All constructor metadata -/
  constructors : Std.HashMap String Nat
  /-- Pre-merge Alloy modules -/
  alloyModules : Array (String × Alloy.Module)

/-- Lower checked modules to Alloy IR and merge with dependencies -/
def lowerAndMerge
    (packageName : String)
    (modules : Array CheckedModule)
    (externalConstructors : Std.HashMap String Nat)
    (mergedGlobals : Soma.Dependent.Globals)
    (dependencyAlloyModules : Array (String × Alloy.Module) := #[])
    : IO (Std.HashMap String Nat × Array (String × Alloy.Module) × Alloy.Module) := do
  IO.println "\n=== Starting compilation phase ==="
  IO.println s!"  Compiling {modules.size} module(s) for package '{packageName}'"

  -- Extract all constructor metadata from modules
  let mut allConstructors : Std.HashMap String Nat := externalConstructors
  for m in modules do
    let ctors := CheckedModule.constructorMetadata m
    for (name, tag) in ctors.toArray do
      allConstructors := allConstructors.insert name tag

  IO.println s!"  Collected {allConstructors.size} constructors"

  -- Lower each module to Alloy IR
  IO.println "  Lowering to Alloy IR..."
  let mut localAlloyModules : Array (String × Alloy.Module) := #[]
  for cm in modules do
    let alloyMod ← lowerToAlloy cm mergedGlobals
    localAlloyModules := localAlloyModules.push (cm.name, alloyMod)

  IO.println s!"  Generated {localAlloyModules.size} local Alloy module(s)"

  -- Combine local modules with dependency modules for merging
  let allAlloyModules := dependencyAlloyModules ++ localAlloyModules

  if dependencyAlloyModules.size > 0 then
    IO.println s!"  Including {dependencyAlloyModules.size} dependency Alloy module(s)"

  -- Merge all Alloy modules into one
  IO.println "  Merging modules..."
  let merged := Alloy.Merge.merge allAlloyModules packageName

  IO.println s!"  Merged module has {merged.funcs.size} function(s)"

  pure (allConstructors, localAlloyModules, merged)

/-- Compile checked modules to a library package -/
def compileLibrary
    (packageName : String)
    (modules : Array CheckedModule)
    (externalConstructors : Std.HashMap String Nat)
    (mergedGlobals : Soma.Dependent.Globals)
    (dependencyAlloyModules : Array (String × Alloy.Module) := #[])
    : IO CompileResult := do
  let (allConstructors, localAlloyModules, _merged) ←
    lowerAndMerge packageName modules externalConstructors mergedGlobals dependencyAlloyModules

  IO.println "Compilation phase complete"

  pure { constructors := allConstructors, alloyModules := localAlloyModules }

/-- Compile checked modules to LLVM IR for an executable -/
def compileModules
    (packageName : String)
    (modules : Array CheckedModule)
    (externalConstructors : Std.HashMap String Nat)
    (mergedGlobals : Soma.Dependent.Globals)
    (dependencyAlloyModules : Array (String × Alloy.Module) := #[])
    (runSomaPasses : Bool := true)
    (targetTriple : Option String := none)
    (targetOs : Soma.Driver.TargetOS)
    (ptrSize : Nat)
    (dataLayout : Option String := none)
    : IO CompileResult := do
  let (allConstructors, localAlloyModules, merged) ←
    lowerAndMerge packageName modules externalConstructors mergedGlobals dependencyAlloyModules

  -- Monomorphize
  IO.println "  Monomorphizing..."
  let mono := (Alloy.Monomorphize.monomorphize merged).rebuildWiredFuncIndex

  IO.println s!"  Monomorphized module has {mono.funcs.size} function(s)"

  let mut optimized := mono
  let mut borrowParamInfo : Std.HashMap Nat (Array Bool) := {}

  let (ioOptimized, ioCount) := Alloy.IOIntrinsics.replaceIOIntrinsics optimized
  optimized := ioOptimized
  if ioCount > 0 then
    IO.println s!"  IO intrinsics: {ioCount} function(s) replaced with erasure-correct bodies"

  let (intrinsicOptimized, intrinsicCount) := Alloy.ListIntrinsics.replaceListIntrinsics optimized
  optimized := intrinsicOptimized
  if intrinsicCount > 0 then
    IO.println s!"  List intrinsics: {intrinsicCount} function(s) replaced with O(1) field access"

  let (elemSizeOptimized, elemSizeCount) := Alloy.ElemSize.refineElemSizes optimized ptrSize
  optimized := elemSizeOptimized
  if elemSizeCount > 0 then
    IO.println s!"  Element size refinement: {elemSizeCount} function(s) refined to exact element sizes"

  optimized := Alloy.ClosureSpec.closureSpec optimized

  if runSomaPasses then
    let (accumOptimized, accumCount) := Alloy.AccumIntro.accumIntro optimized
    optimized := accumOptimized
    if accumCount > 0 then
      IO.println s!"  Accumulator introduction: {accumCount} list-building recursion(s) converted to accumulator style"
    let (arithAccumOptimized, arithAccumCount) := Alloy.ArithAccum.arithAccumIntro optimized
    optimized := arithAccumOptimized
    if arithAccumCount > 0 then
      IO.println s!"  Arithmetic accumulator introduction: {arithAccumCount} recursion(s) converted to accumulator style"
    let (tcoOptimized, tcoCount) := Alloy.TailCall.tailCallOpt optimized
    optimized := tcoOptimized
    if tcoCount > 0 then
      IO.println s!"  Tail call optimization: {tcoCount} self-recursive call(s) converted to loops"
    let (mutualOptimized, mutualCount) := Alloy.TailCall.mutualTailCallOpt optimized
    optimized := mutualOptimized
    if mutualCount > 0 then
      IO.println s!"  Mutual tail call optimization: {mutualCount} cross-function tail call(s) restructured"
    optimized := Alloy.Monomorphize.deadFunctionElimination optimized

    let (consInlined, consCount) := Alloy.ConsInline.inlineConsFastPath optimized
    optimized := consInlined
    if consCount > 0 then
      IO.println s!"  Cons fast-path inlining: {consCount} function(s) with inlined prepend"

    let (borrowed, borrowStats) := Alloy.Borrow.borrowModule optimized
    if borrowStats.borrowedParams > 0 then
      let cloneMsg := if borrowStats.clonesEliminated > 0 then
        s!", {borrowStats.clonesEliminated} clone(s) eliminated"
      else ""
      let narrowMsg := if borrowStats.clonesNarrowed > 0 then
        s!", {borrowStats.clonesNarrowed} clone(s) narrowed"
      else ""
      let eraseMsg := if borrowStats.erasesEliminated > 0 then
        s!", {borrowStats.erasesEliminated} erase(s) eliminated"
      else ""
      IO.println s!"  Borrow analysis: {borrowStats.borrowedParams} parameter(s) borrowed{cloneMsg}{narrowMsg}{eraseMsg}"
    borrowParamInfo := borrowStats.paramInfo

    let (reused, reuseCount) := Alloy.Reuse.reuseModule borrowed ptrSize
    if reuseCount > 0 then
      IO.println s!"  Reuse analysis: {reuseCount} allocation(s) eliminated"
    optimized := reused
  else
    IO.println "  Skipping optimization passes (debug profile)"

  -- Generate LLVM IR
  IO.println "  Generating LLVM IR..."
  let llvmIR := Llvm.codegenToString optimized (targetTriple := targetTriple)
    (targetOs := targetOs) (ptrSize := ptrSize) (borrowInfo := borrowParamInfo)
    (dataLayout := dataLayout)

  IO.println "Compilation phase complete"

  pure { llvmIR := some llvmIR, constructors := allConstructors, alloyModules := localAlloyModules }

/-- Build ProjectMetadata from a ProjectResult for library packaging -/
def buildProjectMetadata (result : ProjectResult) : Metadata.ProjectMetadata :=
  { module := result.packageName
  , symbols := Metadata.symbolEnvToSerializable result.symbols
  , instances := Metadata.instanceMetadataToSerializable result.instances
  , constructors := Metadata.constructorsToSerializable result.constructors
  , globals := Metadata.globalsToSerializable result.globals
  , instanceEnv := Metadata.instanceEnvToSerializable result.instanceEnv
  , abbrevEnv := Metadata.abbrevEnvToSerializable result.abbrevEnv
  }

end Somac.Build
