namespace Somac.Build.External

/-- Configuration for external tool paths -/
structure ToolPaths where
  /-- Path to llc (LLVM static compiler) -/
  llc : String := "llc"
  /-- Path to clang (C/C++ compiler and linker) -/
  clang : String := "clang"
  /-- Path to ar (archive tool) -/
  ar : String := "ar"
  /-- Path to tar (tape archive) -/
  tar : String := "tar"
  /-- Path to the Zig compiler -/
  zig : String := "zig"
  deriving Inhabited

/-- Default tool paths -/
def defaultTools : ToolPaths := {}

/-- The C runtime / object-file ABI the host toolchain produces -/
inductive ClangAbi where
  | gnu
  | msvc
  | other (name : String)
  deriving Inhabited, Repr, BEq

namespace ClangAbi

def name : ClangAbi → String
  | .gnu => "gnu"
  | .msvc => "msvc"
  | .other s => s

instance : ToString ClangAbi := ⟨name⟩

/-- Derive the ABI from a triple's final segment -/
def fromTriple (triple : String) : ClangAbi :=
  let lower := triple.toLower
  if lower.endsWith "-msvc" then .msvc
  else if lower.endsWith "-gnu" || lower.endsWith "-mingw32" then .gnu
  else
    let parts := lower.splitOn "-"
    match parts.getLast? with
    | some last => .other last
    | none => .other ""

end ClangAbi

/-- File name of the runtime archive inside zig-out-<abi> -/
def runtimeArchiveName : String := "libsoma_runtime.a"

def runtimeArchiveFileFor (abi : ClangAbi) : String :=
  s!"libsoma_runtime-{abi.name}.a"

/-- Find the sysroot directory using the standard discovery order -/
def findSysroot (explicit : Option String) : IO (Option System.FilePath) := do
  -- 1. Explicit sysroot
  if let some s := explicit then
    let path : System.FilePath := ⟨s⟩
    if ← path.pathExists then
      return some path

  -- 2. Environment variable
  if let some s ← IO.getEnv "SOMA_SYSROOT" then
    let path : System.FilePath := ⟨s⟩
    if ← path.pathExists then
      return some path

  -- 3. Relative to executable
  let exe ← IO.appPath
  if let some binDir := exe.parent then
    if let some sysroot := binDir.parent then
      let libPath := sysroot / "lib"
      if ← libPath.pathExists then
        return some sysroot

  -- 4. Well-known svm location
  let home? ← do
    if let some h ← IO.getEnv "HOME" then return some h
    if let some h ← IO.getEnv "USERPROFILE" then return some h
    pure none
  if let some home := home? then
    let svmCurrent : System.FilePath := ⟨home⟩ / ".svm" / "current"
    if ← svmCurrent.pathExists then
      let entries ← svmCurrent.readDir
      for entry in entries do
        let candidate := entry.path
        let libPath := candidate / "lib"
        if ← libPath.pathExists then
          return some candidate

  return none

/-- Result of running an external command -/
structure CommandResult where
  exitCode : UInt32
  stdout : String
  stderr : String

/-- Run an external command and capture output -/
def runCommand (cmd : String) (args : Array String) (cwd : Option String := none)
    : IO CommandResult := do
  let proc ← IO.Process.spawn {
    cmd := cmd
    args := args
    cwd := cwd
    stdout := .piped
    stderr := .piped
  }
  let stdout ← proc.stdout.readToEnd
  let stderr ← proc.stderr.readToEnd
  let exitCode ← proc.wait
  pure { exitCode, stdout, stderr }

/-- Query clang for its default target triple -/
def detectClangTriple (tools : ToolPaths) : IO String := do
  let result ← runCommand tools.clang #["-print-target-triple"]
  if result.exitCode == 0 then
    pure result.stdout.trimAscii.toString
  else
    pure ""

/-- Detect clang's default ABI. -/
def detectClangAbi (tools : ToolPaths) : IO ClangAbi := do
  let triple ← detectClangTriple tools
  pure (ClangAbi.fromTriple triple)

/-- Derive the ABI we should target for an artifact -/
def abiForTarget (tools : ToolPaths) (llvmTarget : Option String) : IO ClangAbi := do
  match llvmTarget with
  | some triple =>
    let abi := ClangAbi.fromTriple triple
    match abi with
    | .other _ => detectClangAbi tools
    | _ => pure abi
  | none => detectClangAbi tools

/-- Candidate dev-mode locations for the runtime tree -/
private def devRuntimeDirs : IO (Array System.FilePath) := do
  let cwd ← IO.currentDir
  pure #[cwd / ".." / "runtime", cwd / "runtime"]

/-- Per-ABI install prefix under the runtime source dir -/
private def zigOutDirFor (abi : ClangAbi) : System.FilePath :=
  System.FilePath.mk s!"zig-out-{abi.name}"

/-- Archive path inside an ABI-specific zig-out tree -/
private def zigArchiveSubpathFor (abi : ClangAbi) : System.FilePath :=
  zigOutDirFor abi / runtimeArchiveName

/-- Invoke `zig build` in the runtime source directory -/
private def buildRuntimeArchive
    (zig : String) (runtimeDir : System.FilePath) (abi : ClangAbi)
    : IO (Except String System.FilePath) := do
  let prefixDir := zigOutDirFor abi
  let mut args : Array String := #["build", "-p", prefixDir.toString]
  if System.Platform.isWindows then
    match abi with
    | .gnu  => args := args.push "-Dtarget=x86_64-windows-gnu"
    | .msvc => args := args.push "-Dtarget=x86_64-windows-msvc"
    | .other _ => pure ()
  let result ← runCommand zig args (cwd := some runtimeDir.toString)
  if result.exitCode ≠ 0 then
    pure (.error s!"zig build failed in {runtimeDir} (exit {result.exitCode}):\n{result.stderr}")
  else
    let path := runtimeDir / zigArchiveSubpathFor abi
    if ← path.pathExists then
      pure (.ok path)
    else
      pure (.error s!"zig build succeeded but {path} was not produced")

/-- Find the runtime archive for the requested ABI -/
def findRuntime (sysroot : Option String) (abi : ClangAbi) : IO (Option System.FilePath) := do
  if let some sysrootPath ← findSysroot sysroot then
    let abiPath := sysrootPath / "lib" / runtimeArchiveFileFor abi
    if ← abiPath.pathExists then return some abiPath

  let devDirs ← devRuntimeDirs

  for dir in devDirs do
    let abiZigOut := dir / zigArchiveSubpathFor abi
    if ← abiZigOut.pathExists then return some abiZigOut

  for dir in devDirs do
    let buildZig := dir / "build.zig"
    if ← buildZig.pathExists then
      IO.println s!"runtime archive for {abi} not found; running `zig build` in {dir}"
      match ← buildRuntimeArchive defaultTools.zig dir abi with
      | .ok path => return some path
      | .error e => IO.eprintln e
  return none

/-- Check if a tool is available -/
def checkTool (path : String) : IO Bool := do
  let result ← runCommand "which" #[path]
  pure (result.exitCode == 0)

/-- Compile LLVM IR (.ll) to object file (.o) using clang -/
def compileToObject
    (tools : ToolPaths)
    (llPath : System.FilePath)
    (oPath : System.FilePath)
    (optLevel : Nat := 2)
    (lto : Bool := false)
    (llvmTarget : Option String := none)
    : IO (Except String Unit) := do
  let optFlag := s!"-O{min optLevel 3}"
  let mut args := #[
    "-c", optFlag,
    "-rtlib=compiler-rt",
    "-o", oPath.toString, llPath.toString
  ]

  if lto then
    args := args.push "-flto"

  if let some triple := llvmTarget then
    args := #["-target", triple] ++ args

  let result ← runCommand tools.clang args

  if result.exitCode == 0 then
    pure (.ok ())
  else
    pure (.error s!"clang failed (exit {result.exitCode}):\n{result.stderr}")

/-- Link object files into an executable -/
def linkExecutable
    (tools : ToolPaths)
    (objs : Array System.FilePath)
    (output : System.FilePath)
    (runtime : Option System.FilePath := none)
    (optLevel : Nat := 2)
    (lto : Bool := false)
    (llvmTarget : Option String := none)
    (abi : ClangAbi := .other "")
    : IO (Except String Unit) := do
  let optFlag := s!"-O{min optLevel 3}"

  let mut args := #[optFlag, "-o", output.toString]

  if let some triple := llvmTarget then
    args := #["-target", triple] ++ args

  args := args.push "-rtlib=compiler-rt"

  if lto then
    args := args.push "-flto"

  -- Add object files
  for obj in objs do
    args := args.push obj.toString

  if let some rt := runtime then
    args := args.push rt.toString

  match abi with
  | .gnu => args := args.push "-lgcc"
  | .msvc =>
    args := args.push "-Wl,/subsystem:console"
  | _ => pure ()

  let result ← runCommand tools.clang args
  if result.exitCode == 0 then
    pure (.ok ())
  else
    pure (.error s!"linker failed (exit {result.exitCode}):\n{result.stderr}")

/-- Create a static library archive from object files -/
def createArchive
    (tools : ToolPaths)
    (objs : Array System.FilePath)
    (output : System.FilePath)
    : IO (Except String Unit) := do
  let mut args := #["rcs", output.toString]
  for obj in objs do
    args := args.push obj.toString

  let result ← runCommand tools.ar args

  if result.exitCode == 0 then
    pure (.ok ())
  else
    pure (.error s!"ar failed (exit {result.exitCode}):\n{result.stderr}")

/-- Create a tarball -/
def createTarball
    (tools : ToolPaths)
    (sourceDir : System.FilePath)
    (output : System.FilePath)
    (compressed : Bool := true)
    : IO (Except String Unit) := do
  -- tar -czf output.tar.gz -C parent dirName
  let parent := sourceDir.parent.getD "."
  let dirName := sourceDir.fileName.getD "archive"

  let flags := if compressed then "-czf" else "-cf"
  let args := #[flags, output.toString, "-C", parent.toString, dirName]

  let result ← runCommand tools.tar args

  if result.exitCode == 0 then
    pure (.ok ())
  else
    pure (.error s!"tar failed (exit {result.exitCode}):\n{result.stderr}")

/-- Extract a tarball -/
def extractTarball
    (tools : ToolPaths)
    (archive : System.FilePath)
    (targetDir : System.FilePath)
    : IO (Except String Unit) := do
  -- tar -xf archive.tar.gz -C targetDir
  let args := #["-xf", archive.toString, "-C", targetDir.toString]

  let result ← runCommand tools.tar args

  if result.exitCode == 0 then
    pure (.ok ())
  else
    pure (.error s!"tar failed (exit {result.exitCode}):\n{result.stderr}")

/-- Full compilation pipeline: LLVM IR → object → executable -/
def compileAndLink
    (tools : ToolPaths)
    (llPath : System.FilePath)
    (output : System.FilePath)
    (runtime : Option System.FilePath := none)
    (optLevel : Nat := 2)
    (keepIntermediates : Bool := false)
    (sysroot : Option String := none)
    (lto : Bool := false)
    (llvmTarget : Option String := none)
    : IO (Except String Unit) := do
  let oPath := output.withExtension "o"
  let abi ← abiForTarget tools llvmTarget

  match ← compileToObject tools llPath oPath optLevel lto llvmTarget with
  | .error e => pure (.error e)
  | .ok () =>
    let runtimePath ← match runtime with
      | some r => pure (some r)
      | none => findRuntime sysroot abi

    match ← linkExecutable tools #[oPath] output runtimePath optLevel lto llvmTarget abi with
    | .error e => pure (.error e)
    | .ok () =>
      unless keepIntermediates do
        IO.FS.removeFile oPath |>.catchExceptions fun _ => pure ()
      pure (.ok ())

end Somac.Build.External
