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

/-- Runtime archive name -/
def runtimeArchiveFile : String := "libsoma_runtime.a"

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

/-- Candidate dev-mode locations for the runtime tree -/
private def devRuntimeDirs : IO (Array System.FilePath) := do
  let cwd ← IO.currentDir
  pure #[cwd / ".." / "runtime", cwd / "runtime"]

private def zigArchiveSubpath : System.FilePath :=
  System.FilePath.mk "zig-out" / runtimeArchiveFile

private def buildRuntimeArchive
    (zig : String) (runtimeDir : System.FilePath)
    : IO (Except String System.FilePath) := do
  let result ← runCommand zig #["build"] (cwd := some runtimeDir.toString)
  if result.exitCode ≠ 0 then
    pure (.error s!"zig build failed in {runtimeDir} (exit {result.exitCode}):\n{result.stderr}")
  else
    let path := runtimeDir / zigArchiveSubpath
    if ← path.pathExists then
      pure (.ok path)
    else
      pure (.error s!"zig build succeeded but {path} was not produced")

/-- Find the prebuilt runtime archive -/
def findRuntime (sysroot : Option String) : IO (Option System.FilePath) := do
  if let some sysrootPath ← findSysroot sysroot then
    let runtimePath := sysrootPath / "lib" / runtimeArchiveFile
    if ← runtimePath.pathExists then
      return some runtimePath

  let devDirs ← devRuntimeDirs

  for dir in devDirs do
    let flat := dir / runtimeArchiveFile
    if ← flat.pathExists then return some flat
    let zigOut := dir / zigArchiveSubpath
    if ← zigOut.pathExists then return some zigOut

  for dir in devDirs do
    let buildZig := dir / "build.zig"
    if ← buildZig.pathExists then
      IO.println s!"runtime archive not found; running `zig build` in {dir}"
      match ← buildRuntimeArchive defaultTools.zig dir with
      | .ok path => return some path
      | .error e =>
        IO.eprintln e
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
  let mut args := #["-c", optFlag, "-o", oPath.toString, llPath.toString]

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
    (isWindowsTarget : Bool := System.Platform.isWindows)
    : IO (Except String Unit) := do
  let _ := llvmTarget
  let optFlag := s!"-O{min optLevel 3}"

  let mut args := #[optFlag, "-o", output.toString]

  if lto then
    args := args.push "-flto"

  -- Add object files
  for obj in objs do
    args := args.push obj.toString

  if let some rt := runtime then
    args := args.push rt.toString

  if isWindowsTarget then
    args := args.push "-lgcc"

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
  -- ar rcs output.a obj1.o obj2.o ...
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
    (isWindowsTarget : Bool := System.Platform.isWindows)
    : IO (Except String Unit) := do
  let oPath := output.withExtension "o"

  match ← compileToObject tools llPath oPath optLevel lto llvmTarget with
  | .error e => pure (.error e)
  | .ok () =>
    let runtimePath ← match runtime with
      | some r => pure (some r)
      | none => findRuntime sysroot

    match ← linkExecutable tools #[oPath] output runtimePath optLevel lto llvmTarget isWindowsTarget with
    | .error e => pure (.error e)
    | .ok () =>
      unless keepIntermediates do
        IO.FS.removeFile oPath |>.catchExceptions fun _ => pure ()
      pure (.ok ())

end Somac.Build.External
