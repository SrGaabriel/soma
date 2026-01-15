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
  deriving Inhabited

/-- Default tool paths -/
def defaultTools : ToolPaths := {}

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
  let args := #["-c", optFlag, "-o", oPath.toString, llPath.toString]

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
    args := args.push rt.toString

  -- Add standard libraries (math library often needed)
  args := args.push "-lm"

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
    : IO (Except String Unit) := do
  -- Compile to object
  let oPath := output.withExtension "o"

  match ← compileToObject tools llPath oPath optLevel with
  | .error e => pure (.error e)
  | .ok () =>
    -- Link to executable
    match ← linkExecutable tools #[oPath] output runtime optLevel with
    | .error e => pure (.error e)
    | .ok () =>
      unless keepIntermediates do
        IO.FS.removeFile oPath |>.catchExceptions fun _ => pure ()
      pure (.ok ())

end Somac.Build.External
