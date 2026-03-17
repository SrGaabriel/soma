namespace Somac.Build.External

/-- Configuration for external tool paths -/
structure ToolPaths where
  /-- Path to llc (LLVM static compiler) -/
  llc : String := "llc"
  /-- Path to clang (C/C++ compiler and linker) -/
  clang : String := "clang"
  /-- Path to cc (system C compiler for linking, typically gcc) -/
  cc : String := "cc"
  /-- Path to ar (archive tool) -/
  ar : String := "ar"
  /-- Path to tar (tape archive) -/
  tar : String := "tar"
  deriving Inhabited

/-- Default tool paths -/
def defaultTools : ToolPaths := {}

/-- Runtime file names -/
def runtimeSourceFile : String := "soma_runtime.c"
def runtimeHeaderFile : String := "soma_runtime.h"

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

/-- Find the runtime source file -/
def findRuntime (sysroot : Option String) : IO (Option System.FilePath) := do
  -- 1. Check sysroot/lib/
  if let some sysrootPath ← findSysroot sysroot then
    let runtimePath := sysrootPath / "lib" / runtimeSourceFile
    if ← runtimePath.pathExists then
      return some runtimePath

  -- 2. Check relative to cwd (todo: remove this on prod)
  let cwd ← IO.currentDir
  -- Check ../runtime/ (when running from compiler/)
  let devPath := cwd / ".." / "runtime" / runtimeSourceFile
  if ← devPath.pathExists then
    return some devPath
  -- Check runtime/ (when running from project root)
  let rootPath := cwd / "runtime" / runtimeSourceFile
  if ← rootPath.pathExists then
    return some rootPath

  return none

/-- Result of running an external command -/
structure CommandResult where
  exitCode : UInt32
  stdout : String
  stderr : String

/-- Run an external command and capture output -/
def runCommand (cmd : String) (args : Array String) : IO CommandResult := do
  let proc ← IO.Process.spawn {
    cmd := cmd
    args := args
    stdout := .piped
    stderr := .piped
  }
  let stdout ← proc.stdout.readToEnd
  let stderr ← proc.stderr.readToEnd
  let exitCode ← proc.wait
  pure { exitCode, stdout, stderr }

/-- Check if a tool is available -/
def checkTool (path : String) : IO Bool := do
  let result ← runCommand "which" #[path]
  pure (result.exitCode == 0)

/-- Compile LLVM IR (.ll) to object file (.o) using llc + clang -/
def compileToObject
    (tools : ToolPaths)
    (llPath : System.FilePath)
    (oPath : System.FilePath)
    (optLevel : Nat := 2)
    : IO (Except String Unit) := do
  -- Use clang to compile LLVM IR directly to object
  let optFlag := s!"-O{min optLevel 3}"
  let mut args := #["-c", optFlag, "-o", oPath.toString, llPath.toString]

  -- On Windows, target MinGW to match the linker (gcc uses ___chkstk, MSVC uses __chkstk)
  if System.Platform.isWindows then
    args := #["-target", "x86_64-w64-mingw32"] ++ args

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
    : IO (Except String Unit) := do
  let optFlag := s!"-O{min optLevel 3}"

  -- Build argument list
  let mut args := #[optFlag, "-o", output.toString]

  -- Add object files
  for obj in objs do
    args := args.push obj.toString

  -- Add runtime library if specified
  if let some rt := runtime then
    if let some rtDir := rt.parent then
      args := args ++ #["-I", rtDir.toString]
    args := args.push rt.toString

  -- Add standard libraries (math library often needed)
  args := args.push "-lm"

  -- On Windows, link against libgcc for __chkstk (stack probing for large stack frames)
  if System.Platform.isWindows then
    args := args.push "-lgcc"

  -- Use system cc for linking (todo: reconsider)
  let result ← runCommand tools.cc args

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
    : IO (Except String Unit) := do
  -- Compile to object
  let oPath := output.withExtension "o"

  match ← compileToObject tools llPath oPath optLevel with
  | .error e => pure (.error e)
  | .ok () =>
    -- Find runtime if not explicitly provided
    let runtimePath ← match runtime with
      | some r => pure (some r)
      | none => findRuntime sysroot

    -- Link to executable
    match ← linkExecutable tools #[oPath] output runtimePath optLevel with
    | .error e => pure (.error e)
    | .ok () =>
      unless keepIntermediates do
        IO.FS.removeFile oPath |>.catchExceptions fun _ => pure ()
      pure (.ok ())

end Somac.Build.External
